"""Pytest harness: every fenced ``lean`` / ``lean4`` block in *.md under
the repo root must either compile via ``lake env lean`` or carry an
explicit ``<!-- doctest: ... -->`` skip marker.

Run from the repo root:

    pytest tools/markdown_doctest/test_doctest.py

CI gate is wired in ``.github/workflows/lean-build.yml`` (the
"Markdown doctest" step). Each block runs in its own ``lake env lean``
subprocess; on a warm cache that's ~5s per block. With ~14 compilable
blocks today the gate runs in ~80s, comfortably under the 15-minute
timeout. Past 30 blocks consider parametrising under pytest-xdist.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from .extract import extract_blocks, discover_markdown
from .runner import run_block


REPO_ROOT = Path(__file__).resolve().parents[2]


def _all_blocks():
    """Collect every block under the repo. Pytest parametrize sees this
    once at collection time."""
    out = []
    for p in discover_markdown(REPO_ROOT):
        for b in extract_blocks(p):
            out.append(b)
    return out


# Materialise once so pytest collects deterministically. Test ids use
# the (relative-path, block_idx) pair so failures point at the exact
# fence.
_BLOCKS = _all_blocks()
_IDS = [b.test_id for b in _BLOCKS]


@pytest.mark.parametrize("block", _BLOCKS, ids=_IDS)
def test_markdown_doctest_block(block) -> None:
    """Compile one fenced lean/lean4 block, or skip if it carries a
    doctest skip marker."""
    if block.skip_reason:
        pytest.skip(f"explicit doctest marker: {block.skip_reason}")
    result = run_block(block.body, repo_root=REPO_ROOT, timeout_s=240)
    if not result.ok:
        # Surface the full lake output in the failure so the author
        # doesn't have to re-run by hand. Truncate at 4 KiB to keep
        # pytest reports navigable.
        out = result.stdout
        if len(out) > 4096:
            out = out[:4096] + "\n... [truncated]"
        pytest.fail(
            f"block at {block.path}:{block.start_line} failed to "
            f"compile (exit={result.exit_code}, "
            f"elapsed={result.elapsed_ms}ms).\n\n"
            f"Either fix the block (add imports, etc.) or mark it with\n"
            f"  <!-- doctest: skip-reason: <why> -->\n"
            f"immediately before the fence.\n\n"
            f"--- lake output ---\n{out}"
        )


def test_at_least_one_compilable_block_exists() -> None:
    """Sanity gate. If every block in the repo got marked skip the
    harness is silently testing nothing — fail loud rather than green-
    by-default."""
    compilable = [b for b in _BLOCKS if b.skip_reason is None]
    assert compilable, (
        "no compilable lean/lean4 blocks found; either every block "
        "got marked skip (likely an over-eager refactor) or the "
        "extraction broke. Investigate before merging."
    )
