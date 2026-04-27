#!/usr/bin/env python3
"""tools/refresh_readme_stats.py — regenerate the auto-tracked stats
block in README.md from the canonical `tools/sim/theorem_manifest.py`.

The README has a sentinel-bracketed block:

    <!-- pythia-stats-auto-begin -->
    ...
    <!-- pythia-stats-auto-end -->

This script rewrites the body between those sentinels with the current
theorem count + sorted domain list. Run after adding theorems to the
manifest:

    python3 tools/refresh_readme_stats.py

Exits 0 on a successful (idempotent) update, 0 if nothing changed,
1 if the sentinels are missing or the README is malformed.

The companion drift test at `tools/sim/test_readme_drift.py` enforces
that the block is in sync with the manifest, so CI fails any PR that
adds a theorem without running this script.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional


REPO_ROOT = Path(__file__).resolve().parent.parent
README_PATH = REPO_ROOT / "README.md"

BEGIN_SENTINEL = "<!-- pythia-stats-auto-begin -->"
END_SENTINEL = "<!-- pythia-stats-auto-end -->"


def _import_manifest():
    """Local import so this script works as a standalone CLI without
    requiring the caller to first set sys.path."""
    sys.path.insert(0, str(REPO_ROOT))
    from tools.sim.theorem_manifest import MANIFEST, domains  # noqa: E402
    return MANIFEST, domains()


def render_stats_block(count: int, sorted_domains: list[str]) -> str:
    """Return the body that goes BETWEEN the sentinel markers.

    Format is intentionally simple so the drift test can parse counts
    deterministically without HTML-comment quirks: a single line with
    two integers in known positions, plus a parenthetical domain list.
    """
    n_domains = len(sorted_domains)
    domain_csv = ", ".join(sorted_domains)
    return (
        f"**Coverage**: {count} cross-domain theorems shipped "
        f"across {n_domains} domains\n"
        f"({domain_csv}). Auto-tracked\n"
        f"in [`tools/sim/theorem_manifest.py`](tools/sim/theorem_manifest.py); "
        f"regenerate this block via `python3 tools/refresh_readme_stats.py`."
    )


def rewrite_block(
    readme_text: str,
    count: int,
    sorted_domains: list[str],
) -> str:
    """Return README text with the stats block rewritten in place.
    Raises ValueError if either sentinel is missing.
    """
    begin = readme_text.find(BEGIN_SENTINEL)
    end = readme_text.find(END_SENTINEL)
    if begin == -1:
        raise ValueError(f"missing begin sentinel {BEGIN_SENTINEL!r}")
    if end == -1:
        raise ValueError(f"missing end sentinel {END_SENTINEL!r}")
    if end < begin:
        raise ValueError("end sentinel appears before begin sentinel")
    body = render_stats_block(count, sorted(sorted_domains))
    new_text = (
        readme_text[: begin + len(BEGIN_SENTINEL)]
        + "\n"
        + body
        + "\n"
        + readme_text[end:]
    )
    return new_text


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check", action="store_true",
                   help="exit 1 without writing if README is stale")
    p.add_argument("--readme", default=str(README_PATH),
                   help="path to README.md (for tests)")
    args = p.parse_args(argv)

    readme_path = Path(args.readme)
    manifest, doms = _import_manifest()
    count = len(manifest)
    sorted_domains = sorted(set(doms))
    current = readme_path.read_text()
    try:
        rewritten = rewrite_block(current, count, sorted_domains)
    except ValueError as e:
        print(f"refresh_readme_stats: {e}", file=sys.stderr)
        return 1

    if rewritten == current:
        print(f"README stats block is already in sync ({count} theorems, "
              f"{len(sorted_domains)} domains).")
        return 0

    if args.check:
        print(
            f"README stats block is STALE — manifest has {count} theorems, "
            f"{len(sorted_domains)} domains. "
            f"Run `python3 tools/refresh_readme_stats.py` to fix.",
            file=sys.stderr,
        )
        return 1

    readme_path.write_text(rewritten)
    print(f"README stats block updated: {count} theorems, "
          f"{len(sorted_domains)} domains.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
