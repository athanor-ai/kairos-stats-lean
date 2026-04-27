"""tools/sim/test_readme_drift.py — drift test for the auto-tracked
stats block in README.md.

Fails any PR that adds (or removes) theorems from
`tools/sim/theorem_manifest.MANIFEST` without running
`python3 tools/refresh_readme_stats.py`. Catches the cheapest possible
flavour of README rot: stale numbers in the headline.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.refresh_readme_stats import (  # noqa: E402
    BEGIN_SENTINEL,
    END_SENTINEL,
    count_pythia_decls,
    count_stat_lemmas,
    render_stats_block,
    rewrite_block,
)
from tools.sim.theorem_manifest import MANIFEST, domains  # noqa: E402


README_PATH = REPO_ROOT / "README.md"


# ── pure helpers ────────────────────────────────────────────────────

def test_render_stats_block_includes_sim_count():
    body = render_stats_block(7, ["bio", "chem"])
    assert "7 cross-domain theorems" in body


def test_render_stats_block_includes_domain_count():
    body = render_stats_block(0, ["a", "b", "c"])
    assert "across 3 domains" in body


def test_render_stats_block_lists_domains_csv():
    body = render_stats_block(0, ["alpha", "bravo", "charlie"])
    assert "(alpha, bravo, charlie)" in body


def test_render_stats_block_zero_is_valid():
    body = render_stats_block(0, [])
    assert "0 cross-domain theorems" in body
    assert "across 0 domains" in body


def test_render_stats_block_includes_total_decls_when_passed():
    body = render_stats_block(5, ["bio"], total_decls=464, stat_lemma_count=55)
    assert "464 theorem/lemma declarations" in body
    assert "55 `@[stat_lemma]`-tagged" in body


def test_render_stats_block_omits_total_when_none():
    body = render_stats_block(5, ["bio"])
    assert "theorem/lemma declarations" not in body
    assert "@[stat_lemma]" not in body


def test_rewrite_block_replaces_only_between_sentinels():
    src = (
        "header\n"
        f"{BEGIN_SENTINEL}\n"
        "OLD CONTENT\n"
        f"{END_SENTINEL}\n"
        "footer\n"
    )
    out = rewrite_block(src, 5, ["bio"])
    assert "header" in out
    assert "footer" in out
    assert "OLD CONTENT" not in out
    assert "5 cross-domain theorems" in out


def test_rewrite_block_raises_on_missing_begin():
    src = f"some text\n{END_SENTINEL}\nmore\n"
    with pytest.raises(ValueError, match="begin sentinel"):
        rewrite_block(src, 0, [])


def test_rewrite_block_raises_on_missing_end():
    src = f"some text\n{BEGIN_SENTINEL}\nmore\n"
    with pytest.raises(ValueError, match="end sentinel"):
        rewrite_block(src, 0, [])


def test_rewrite_block_raises_on_swapped_sentinels():
    src = f"{END_SENTINEL}\nbody\n{BEGIN_SENTINEL}\n"
    with pytest.raises(ValueError, match="before begin"):
        rewrite_block(src, 0, [])


def test_rewrite_block_is_idempotent():
    """Applying the rewrite twice yields the same text the second
    time — running `refresh_readme_stats` repeatedly is safe."""
    src = (
        f"{BEGIN_SENTINEL}\n"
        "stale\n"
        f"{END_SENTINEL}\n"
    )
    once = rewrite_block(src, 4, ["bio", "chem"], total_decls=10, stat_lemma_count=2)
    twice = rewrite_block(once, 4, ["bio", "chem"], total_decls=10, stat_lemma_count=2)
    assert once == twice


# ── source counters ─────────────────────────────────────────────────

def test_count_pythia_decls_skips_scratch(tmp_path):
    pythia = tmp_path / "Pythia"
    pythia.mkdir()
    (pythia / "Real.lean").write_text(
        "theorem foo : True := trivial\nlemma bar : True := trivial\n"
    )
    scratch = pythia / "Scratch"
    scratch.mkdir()
    (scratch / "Junk.lean").write_text(
        "theorem ignored : True := trivial\n"
    )
    n = count_pythia_decls(tmp_path)
    assert n == 2


def test_count_stat_lemmas_finds_attribute_uses(tmp_path):
    pythia = tmp_path / "Pythia"
    pythia.mkdir()
    (pythia / "X.lean").write_text(
        "@[stat_lemma]\ntheorem foo : True := trivial\n"
        "@[stat_lemma]\nlemma bar : True := trivial\n"
        "theorem unrelated : True := trivial\n"
    )
    scratch = pythia / "Scratch"
    scratch.mkdir()
    (scratch / "Y.lean").write_text(
        "@[stat_lemma]\ntheorem ignored : True := trivial\n"
    )
    assert count_stat_lemmas(tmp_path) == 2


def test_count_pythia_decls_zero_when_no_pythia(tmp_path):
    """No Pythia/ directory → 0, not an error."""
    assert count_pythia_decls(tmp_path) == 0
    assert count_stat_lemmas(tmp_path) == 0


# ── against the real README ─────────────────────────────────────────

def test_readme_has_sentinels():
    """Catches accidental removal of the auto-block during README
    rewrites; the refresh script needs both sentinels to function."""
    text = README_PATH.read_text()
    assert BEGIN_SENTINEL in text, (
        f"README is missing {BEGIN_SENTINEL!r}; the auto-tracked stats "
        f"block is gone, refresh_readme_stats.py cannot run"
    )
    assert END_SENTINEL in text


def test_readme_stats_in_sync_with_manifest():
    """Headline drift test: the counts rendered between the README
    sentinels must equal what the live source says today (manifest +
    grep over Pythia/).

    On failure: run `python3 tools/refresh_readme_stats.py`.
    """
    current = README_PATH.read_text()
    expected = rewrite_block(
        current, len(MANIFEST), sorted(set(domains())),
        total_decls=count_pythia_decls(),
        stat_lemma_count=count_stat_lemmas(),
    )
    if current != expected:
        # Surface the diff inline so the failing CI log tells the
        # contributor exactly what's stale.
        import difflib
        diff = "\n".join(difflib.unified_diff(
            current.splitlines(),
            expected.splitlines(),
            fromfile="README.md (current)",
            tofile="README.md (expected, per manifest)",
            lineterm="",
        ))
        pytest.fail(
            "README stats block is stale relative to "
            "tools/sim/theorem_manifest.MANIFEST.\n"
            "Run `python3 tools/refresh_readme_stats.py` to fix.\n\n"
            f"{diff}"
        )


def test_check_mode_exits_1_on_stale(tmp_path, monkeypatch):
    """`refresh_readme_stats.py --check` returns 1 when README would be
    rewritten by a real run (i.e., it is stale)."""
    fake_readme = tmp_path / "README.md"
    fake_readme.write_text(
        "header\n"
        f"{BEGIN_SENTINEL}\n"
        "stale stats — count claims 0\n"
        f"{END_SENTINEL}\n"
        "footer\n"
    )
    from tools.refresh_readme_stats import main as refresh_main
    rc = refresh_main(["--check", "--readme", str(fake_readme)])
    assert rc == 1
    # Did not modify the file.
    assert "stale stats" in fake_readme.read_text()


def test_check_mode_exits_0_on_in_sync(tmp_path):
    """`--check` returns 0 when the README already matches the
    manifest (fixture builds the block from the live manifest first)."""
    fake_readme = tmp_path / "README.md"
    body = render_stats_block(
        len(MANIFEST), sorted(set(domains())),
        total_decls=count_pythia_decls(),
        stat_lemma_count=count_stat_lemmas(),
    )
    fake_readme.write_text(
        f"head\n{BEGIN_SENTINEL}\n{body}\n{END_SENTINEL}\nfoot\n"
    )
    from tools.refresh_readme_stats import main as refresh_main
    rc = refresh_main(["--check", "--readme", str(fake_readme)])
    assert rc == 0
