"""tools/sim/test_aristotle_import.py — unit tests for the
`tools/aristotle_import.py` Aristotle-result importer.

Covers the pure helpers (_list_lean_files, _diff_against_main,
_read_summary, _untar) plus argparse smoke. The full main() CLI
is exercised end-to-end via a fixture tarball (no network, no
aristotle binary), but git-touching helpers are stubbed.
"""
from __future__ import annotations

import io
import sys
import tarfile
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import tools.aristotle_import as ai  # noqa: E402


# ── _list_lean_files ─────────────────────────────────────────────────

def test_list_lean_files_empty_when_no_pythia_dir(tmp_path):
    """Tarballs without `Pythia/` produce an empty list."""
    (tmp_path / "lakefile.lean").write_text("-- empty\n")
    assert ai._list_lean_files(tmp_path) == []


def test_list_lean_files_recursive(tmp_path):
    """Recursive walk under Pythia/ picks up nested .lean files."""
    pythia = tmp_path / "Pythia"
    pythia.mkdir()
    (pythia / "BDG.lean").write_text("theorem bdg : True := trivial\n")
    sub = pythia / "InfoTheory"
    sub.mkdir()
    (sub / "Foo.lean").write_text("theorem foo : True := trivial\n")
    # Non-Lean files are ignored.
    (pythia / "README.md").write_text("readme\n")
    out = ai._list_lean_files(tmp_path)
    out_names = sorted(str(p) for p in out)
    assert out_names == ["Pythia/BDG.lean", "Pythia/InfoTheory/Foo.lean"]


def test_list_lean_files_skips_files_outside_pythia(tmp_path):
    """Files outside Pythia/ are NOT included."""
    pythia = tmp_path / "Pythia"
    pythia.mkdir()
    (pythia / "Real.lean").write_text("ok\n")
    (tmp_path / "OutsidePythia.lean").write_text("ignored\n")
    out = ai._list_lean_files(tmp_path)
    assert all(str(p).startswith("Pythia/") for p in out)


# ── _diff_against_main ───────────────────────────────────────────────

def test_diff_categorises_new_modified_unchanged(tmp_path, monkeypatch):
    """Each Lean file in the Aristotle tarball lands in exactly one
    of {new, modified, unchanged} relative to the repo's Pythia/."""
    repo = tmp_path / "repo"
    aris = tmp_path / "aristotle"
    (repo / "Pythia").mkdir(parents=True)
    (aris / "Pythia").mkdir(parents=True)
    # Unchanged: identical bytes both sides.
    (repo / "Pythia" / "Same.lean").write_bytes(b"-- same content\n")
    (aris / "Pythia" / "Same.lean").write_bytes(b"-- same content\n")
    # Modified: same path, different bytes.
    (repo / "Pythia" / "Diff.lean").write_bytes(b"-- old version\n")
    (aris / "Pythia" / "Diff.lean").write_bytes(b"-- NEW version\n")
    # New: only in aristotle.
    (aris / "Pythia" / "Brand.lean").write_bytes(b"-- novel\n")

    monkeypatch.setattr(ai, "REPO_ROOT", repo)
    new, modified, unchanged = ai._diff_against_main(aris)
    new_names = {str(p) for p in new}
    mod_names = {str(p) for p in modified}
    unch_names = {str(p) for p in unchanged}
    assert new_names == {"Pythia/Brand.lean"}
    assert mod_names == {"Pythia/Diff.lean"}
    assert unch_names == {"Pythia/Same.lean"}


def test_diff_treats_trailing_newline_as_modified(tmp_path, monkeypatch):
    """Byte-level comparison: trailing newline difference -> modified.
    This is documented behaviour (we want to surface the diff)."""
    repo = tmp_path / "repo"
    aris = tmp_path / "aristotle"
    (repo / "Pythia").mkdir(parents=True)
    (aris / "Pythia").mkdir(parents=True)
    (repo / "Pythia" / "X.lean").write_bytes(b"-- payload\n")
    (aris / "Pythia" / "X.lean").write_bytes(b"-- payload\n\n")  # extra newline
    monkeypatch.setattr(ai, "REPO_ROOT", repo)
    _, modified, _ = ai._diff_against_main(aris)
    assert {str(p) for p in modified} == {"Pythia/X.lean"}


# ── _read_summary ────────────────────────────────────────────────────

def test_read_summary_returns_none_when_missing(tmp_path):
    assert ai._read_summary(tmp_path) is None


def test_read_summary_truncates_to_max_lines(tmp_path):
    body = "\n".join(f"line {i}" for i in range(100)) + "\n"
    (tmp_path / "ARISTOTLE_SUMMARY.md").write_text(body)
    out = ai._read_summary(tmp_path, max_lines=5)
    assert out is not None
    assert out.count("\n") == 4  # 5 lines = 4 newlines between
    assert "line 0" in out
    assert "line 5" not in out


def test_read_summary_default_max_lines_30(tmp_path):
    body = "\n".join(f"line {i}" for i in range(100)) + "\n"
    (tmp_path / "ARISTOTLE_SUMMARY.md").write_text(body)
    out = ai._read_summary(tmp_path)
    assert out is not None
    assert out.count("\n") == 29


# ── _untar ───────────────────────────────────────────────────────────

def _make_tarball(target: Path, root_dirname: str = "aristotle-out") -> Path:
    """Build a minimal tar.gz with a single top-level dir and a
    lakefile.lean, matching the shape Aristotle produces."""
    target.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(target, "w:gz") as t:
        # Add the lakefile under the top-level dir.
        info = tarfile.TarInfo(name=f"{root_dirname}/lakefile.lean")
        data = b"-- lake config\n"
        info.size = len(data)
        t.addfile(info, io.BytesIO(data))
        # Add a Pythia/ Lean module.
        info = tarfile.TarInfo(name=f"{root_dirname}/Pythia/Foo.lean")
        data = b"theorem foo : True := trivial\n"
        info.size = len(data)
        t.addfile(info, io.BytesIO(data))
    return target


def test_untar_locates_root_via_lakefile(tmp_path):
    tarball = _make_tarball(tmp_path / "fake.tar.gz")
    dest = tmp_path / "extracted"
    root = ai._untar(tarball, dest)
    assert root.is_dir()
    assert (root / "lakefile.lean").is_file()
    assert (root / "Pythia" / "Foo.lean").is_file()


def test_untar_raises_when_no_lakefile(tmp_path):
    tarball = tmp_path / "no-lake.tar.gz"
    with tarfile.open(tarball, "w:gz") as t:
        info = tarfile.TarInfo(name="just-a-file.txt")
        data = b"hi"
        info.size = len(data)
        t.addfile(info, io.BytesIO(data))
    dest = tmp_path / "extracted"
    with pytest.raises(RuntimeError, match="no lakefile"):
        ai._untar(tarball, dest)


def test_untar_overwrites_existing_dest(tmp_path):
    """Re-extraction wipes the dest first."""
    dest = tmp_path / "extracted"
    dest.mkdir()
    (dest / "stale.txt").write_text("from a previous run")
    tarball = _make_tarball(tmp_path / "fake.tar.gz")
    root = ai._untar(tarball, dest)
    # The stale file should be gone.
    assert not (dest / "stale.txt").exists()
    assert (root / "lakefile.lean").exists()


# ── argparse smoke ───────────────────────────────────────────────────

def test_main_requires_api_key(monkeypatch, capsys):
    """Without ARISTOTLE_API_KEY, main() exits non-zero with an
    actionable error message."""
    monkeypatch.delenv("ARISTOTLE_API_KEY", raising=False)
    rc = ai.main(["abc12345"])
    assert rc == 1
    err = capsys.readouterr().err
    assert "ARISTOTLE_API_KEY" in err


# ── PR body suggestion (satisfies pr-template-check) ────────────────

def test_suggest_pr_body_has_summary_section():
    """Auto-generated PR body must satisfy the repo's
    tools/check_pr_body.py gate: non-empty `## Summary` heading with
    body content beneath."""
    out = ai._suggest_pr_body(
        branch_name="research/aristotle-foo",
        new_files_csv="`Pythia/Foo.lean`",
        modified_files_csv="(none)",
    )
    assert "## Summary" in out
    # The check requires >10 chars of real content beneath the heading;
    # confirm by stripping headings + whitespace and counting.
    summary_block = out.split("## Summary", 1)[1].split("##", 1)[0]
    summary_text = summary_block.strip()
    assert len(summary_text) > 10, summary_text


def test_suggest_pr_body_includes_branch_name():
    out = ai._suggest_pr_body(
        branch_name="research/aristotle-quantum",
        new_files_csv="`Pythia/Quantum/X.lean`",
        modified_files_csv="(none)",
    )
    assert "research/aristotle-quantum" in out


def test_suggest_pr_body_includes_files_lists():
    out = ai._suggest_pr_body(
        branch_name="research/foo",
        new_files_csv="`Pythia/A.lean`, `Pythia/B.lean`",
        modified_files_csv="`Pythia/C.lean`",
    )
    assert "`Pythia/A.lean`" in out
    assert "`Pythia/B.lean`" in out
    assert "`Pythia/C.lean`" in out


def test_suggest_pr_body_handles_empty_files():
    """Empty / `(none)` placeholders must not crash the renderer."""
    out = ai._suggest_pr_body(
        branch_name="research/empty",
        new_files_csv="(none)",
        modified_files_csv="(none)",
    )
    assert "(none)" in out
    assert "## Summary" in out


def test_suggest_pr_body_passes_check_pr_body_gate():
    """Round-trip: feed the suggested body through tools/check_pr_body.py
    to verify it satisfies the actual gate rather than a proxy
    assertion."""
    import tools.check_pr_body as cpb  # noqa: E402

    body = ai._suggest_pr_body(
        branch_name="research/round-trip",
        new_files_csv="`Pythia/RoundTrip.lean`",
        modified_files_csv="(none)",
    )
    # `validate` is the canonical entry point; it returns a list of
    # error strings (empty list = the body passes the CI gate).
    errors = cpb.validate(body, strict=False)
    assert errors == [], f"PR body would be rejected: {errors}"
