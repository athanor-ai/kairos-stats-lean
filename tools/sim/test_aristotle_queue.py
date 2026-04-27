"""tools/sim/test_aristotle_queue.py — unit tests for the Aristotle
queue restock/dashboard CLI at `tools/aristotle_queue.py`.

Mocks all subprocess interaction with the `aristotle` binary so tests
run offline and deterministically. State files are written into
`tmp_path` rather than the real `.aristotle/queue_state.json`.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import tools.aristotle_queue as aq  # noqa: E402


# ── State persistence ────────────────────────────────────────────────

def test_queue_state_round_trip(tmp_path):
    state = aq.QueueState()
    state.targets["foo"] = aq.TargetEntry(
        name="foo", lean_path="Pythia/Foo.lean", project_id="abc", status="QUEUED"
    )
    p = tmp_path / "state.json"
    state.save(p)
    reloaded = aq.QueueState.load(p)
    assert reloaded.targets["foo"].project_id == "abc"
    assert reloaded.targets["foo"].status == "QUEUED"


def test_queue_state_load_empty_when_missing(tmp_path):
    state = aq.QueueState.load(tmp_path / "missing.json")
    assert state.targets == {}


def test_queue_state_save_creates_parent(tmp_path):
    state = aq.QueueState()
    state.targets["x"] = aq.TargetEntry(name="x", lean_path="Pythia/X.lean")
    nested = tmp_path / "deeper" / "still" / "state.json"
    state.save(nested)
    assert nested.is_file()


# ── Target discovery ─────────────────────────────────────────────────

def _scaffold_repo(tmp_path: Path) -> Path:
    """Build a minimal Pythia/ tree with one sorry-bearing file and one
    fully-proven file, then return the repo root."""
    (tmp_path / "Pythia").mkdir()
    (tmp_path / "Pythia" / "WithSorry.lean").write_text(
        "namespace Pythia\n"
        "theorem foo_pending : 0 ≤ 0 := by sorry\n"
        "end Pythia\n"
    )
    (tmp_path / "Pythia" / "Closed.lean").write_text(
        "namespace Pythia\n"
        "theorem bar_closed : 0 ≤ 0 := le_refl 0\n"
        "end Pythia\n"
    )
    sub = tmp_path / "Pythia" / "Sub"
    sub.mkdir()
    (sub / "Nested.lean").write_text(
        "namespace Pythia.Sub\n"
        "lemma baz_pending : True := by sorry\n"
        "end Pythia.Sub\n"
    )
    return tmp_path


def test_discover_finds_sorry_files_only(tmp_path):
    repo = _scaffold_repo(tmp_path)
    targets = aq.discover_targets(repo)
    paths = {t.lean_path for t in targets}
    assert "Pythia/WithSorry.lean" in paths
    assert "Pythia/Closed.lean" not in paths
    assert "Pythia/Sub/Nested.lean" in paths


def test_discover_uses_first_decl_for_name(tmp_path):
    repo = _scaffold_repo(tmp_path)
    targets = aq.discover_targets(repo)
    by_path = {t.lean_path: t for t in targets}
    assert by_path["Pythia/WithSorry.lean"].name.endswith("__foo_pending")
    assert by_path["Pythia/Sub/Nested.lean"].name.endswith("__baz_pending")


def test_discover_skips_files_without_decls(tmp_path):
    """Files with sorry but no theorem/lemma are skipped (e.g. comments)."""
    (tmp_path / "Pythia").mkdir()
    (tmp_path / "Pythia" / "OnlyComment.lean").write_text(
        "-- This file has the word sorry in a comment\n"
        "-- but no actual theorem or lemma decl.\n"
    )
    targets = aq.discover_targets(tmp_path)
    assert targets == []


def test_discover_returns_sorted(tmp_path):
    """Discovery output is path-sorted for deterministic CLI display."""
    repo = _scaffold_repo(tmp_path)
    targets = aq.discover_targets(repo)
    paths = [t.lean_path for t in targets]
    assert paths == sorted(paths)


# ── Aristotle CLI shims ──────────────────────────────────────────────

def _completed(stdout: str = "", stderr: str = "", returncode: int = 0):
    """Build a fake CompletedProcess for monkey-patched subprocess."""
    class P:
        pass
    p = P()
    p.returncode = returncode
    p.stdout = stdout
    p.stderr = stderr
    return p


def test_aristotle_submit_extracts_project_id(monkeypatch, tmp_path):
    fake_uuid = "ff404663-3852-4eeb-b1df-b562fcb01c8a"
    monkeypatch.setattr(aq, "_run", lambda cmd, **kw: _completed(
        stdout=f"Submitted project {fake_uuid}\n"
    ))
    pid = aq.aristotle_submit("solve me", tmp_path)
    assert pid == fake_uuid


def test_aristotle_submit_returns_none_on_failure(monkeypatch, tmp_path):
    monkeypatch.setattr(aq, "_run", lambda cmd, **kw: _completed(
        returncode=1, stderr="boom"
    ))
    pid = aq.aristotle_submit("solve me", tmp_path)
    assert pid is None


def test_aristotle_submit_returns_none_on_unparseable(monkeypatch, tmp_path):
    """If the CLI succeeded but emitted no UUID, callers get None."""
    monkeypatch.setattr(aq, "_run", lambda cmd, **kw: _completed(
        stdout="ok!\n"
    ))
    pid = aq.aristotle_submit("solve me", tmp_path)
    assert pid is None


def test_aristotle_list_status_parses_table(monkeypatch):
    fake_out = (
        "ID                                  STATUS         CREATED\n"
        "ff404663-3852-4eeb-b1df-b562fcb01c8a   COMPLETE   2026-04-26\n"
        "11111111-2222-3333-4444-555555555555   IN_PROGRESS   2026-04-27\n"
        "76112fd4-aaaa-bbbb-cccc-dddddddddddd   FAILED   2026-04-25\n"
    )
    monkeypatch.setattr(aq, "_run", lambda cmd, **kw: _completed(stdout=fake_out))
    out = aq.aristotle_list_status()
    assert out["ff404663-3852-4eeb-b1df-b562fcb01c8a"] == "COMPLETE"
    assert out["11111111-2222-3333-4444-555555555555"] == "IN_PROGRESS"
    assert out["76112fd4-aaaa-bbbb-cccc-dddddddddddd"] == "FAILED"


def test_aristotle_list_status_empty_on_failure(monkeypatch):
    monkeypatch.setattr(aq, "_run", lambda cmd, **kw: _completed(
        returncode=1, stderr="api down"
    ))
    assert aq.aristotle_list_status() == {}


# ── CLI commands ─────────────────────────────────────────────────────

@pytest.fixture
def isolated_state(tmp_path, monkeypatch):
    """Re-point STATE_PATH at a fresh per-test file."""
    p = tmp_path / "queue_state.json"
    monkeypatch.setattr(aq, "STATE_PATH", p)
    return p


def test_main_requires_api_key_for_restock(monkeypatch, capsys, isolated_state):
    monkeypatch.delenv("ARISTOTLE_API_KEY", raising=False)
    rc = aq.main(["restock"])
    assert rc == 1
    err = capsys.readouterr().err
    assert "ARISTOTLE_API_KEY" in err


def test_main_does_not_require_key_for_list(monkeypatch, isolated_state):
    """The `list` command works offline."""
    monkeypatch.delenv("ARISTOTLE_API_KEY", raising=False)
    rc = aq.main(["list"])
    assert rc == 0


def test_main_does_not_require_key_for_discover(
    monkeypatch, tmp_path, isolated_state
):
    monkeypatch.delenv("ARISTOTLE_API_KEY", raising=False)
    repo = _scaffold_repo(tmp_path)
    monkeypatch.setattr(aq, "REPO_ROOT", repo)
    rc = aq.main(["discover"])
    assert rc == 0


def test_dry_run_restock_does_not_call_submit(
    monkeypatch, isolated_state, tmp_path
):
    repo = _scaffold_repo(tmp_path)
    monkeypatch.setattr(aq, "REPO_ROOT", repo)
    monkeypatch.setenv("ARISTOTLE_API_KEY", "test")
    aq.main(["discover"])  # populate state
    # If submit were called in dry-run, this would raise.
    monkeypatch.setattr(aq, "aristotle_submit", lambda *a, **k:
                        (_ for _ in ()).throw(AssertionError("should not run")))
    rc = aq.main(["--dry-run", "restock", "--limit", "5"])
    assert rc == 0


def test_check_updates_status_for_in_flight(
    monkeypatch, isolated_state
):
    state = aq.QueueState.load(isolated_state)
    state.targets["t1"] = aq.TargetEntry(
        name="t1", lean_path="Pythia/T1.lean",
        project_id="ff404663-3852-4eeb-b1df-b562fcb01c8a",
        status="QUEUED",
    )
    state.save(isolated_state)
    monkeypatch.setenv("ARISTOTLE_API_KEY", "test")
    monkeypatch.setattr(aq, "aristotle_list_status",
                        lambda: {"ff404663-3852-4eeb-b1df-b562fcb01c8a": "COMPLETE"})
    rc = aq.main(["check"])
    assert rc == 0
    after = aq.QueueState.load(isolated_state)
    assert after.targets["t1"].status == "COMPLETE"
    assert after.targets["t1"].updated_at is not None


def test_status_command_prints_target_fields(
    monkeypatch, isolated_state, capsys
):
    state = aq.QueueState.load(isolated_state)
    state.targets["foo"] = aq.TargetEntry(
        name="foo", lean_path="Pythia/Foo.lean",
        project_id="some-uuid", status="IN_PROGRESS",
    )
    state.save(isolated_state)
    rc = aq.main(["status", "foo"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "Pythia/Foo.lean" in out
    assert "some-uuid" in out
    assert "IN_PROGRESS" in out


def test_status_command_returns_1_for_unknown(
    monkeypatch, isolated_state, capsys
):
    rc = aq.main(["status", "nonexistent"])
    assert rc == 1
    err = capsys.readouterr().err
    assert "nonexistent" in err


def test_reset_removes_target(monkeypatch, isolated_state):
    state = aq.QueueState.load(isolated_state)
    state.targets["zap"] = aq.TargetEntry(name="zap", lean_path="Pythia/Z.lean")
    state.save(isolated_state)
    rc = aq.main(["reset", "zap"])
    assert rc == 0
    after = aq.QueueState.load(isolated_state)
    assert "zap" not in after.targets


def test_import_completed_lists_complete_targets(
    monkeypatch, isolated_state, capsys
):
    state = aq.QueueState.load(isolated_state)
    state.targets["done"] = aq.TargetEntry(
        name="done", lean_path="Pythia/Done.lean",
        project_id="aaa", status="COMPLETE",
    )
    state.targets["pending"] = aq.TargetEntry(
        name="pending", lean_path="Pythia/Pending.lean",
        project_id="bbb", status="IN_PROGRESS",
    )
    state.save(isolated_state)
    rc = aq.main(["import-completed"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "aaa" in out          # COMPLETE project id is listed
    assert "done" in out         # COMPLETE target name is listed
    assert "bbb" not in out      # IN_PROGRESS project id is NOT listed
    # The bare token "pending" appears in the header line "pending import"
    # so check the IN_PROGRESS target name (`pending`) in commented form.
    assert "# pending" not in out
