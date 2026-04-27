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


_DECL_RE = __import__("re").compile(r"^(?:theorem|lemma)\s+", __import__("re").MULTILINE)
_STAT_LEMMA_RE = __import__("re").compile(
    r"^@\[stat_lemma\]", __import__("re").MULTILINE
)


def count_pythia_decls(repo_root: Path = REPO_ROOT) -> int:
    """Count `^theorem ` + `^lemma ` declarations across Pythia/,
    excluding Pythia/Scratch/. The total surface size — every
    statement claimed in the library, sorry-bearing or not."""
    pythia_dir = repo_root / "Pythia"
    if not pythia_dir.is_dir():
        return 0
    total = 0
    for p in pythia_dir.rglob("*.lean"):
        if "Scratch" in p.parts:
            continue
        total += len(_DECL_RE.findall(p.read_text()))
    return total


def count_stat_lemmas(repo_root: Path = REPO_ROOT) -> int:
    """Count `@[stat_lemma]` attribute uses across Pythia/. The size
    of the cascade: what `pythia` tactic dispatches to."""
    pythia_dir = repo_root / "Pythia"
    if not pythia_dir.is_dir():
        return 0
    total = 0
    for p in pythia_dir.rglob("*.lean"):
        if "Scratch" in p.parts:
            continue
        total += len(_STAT_LEMMA_RE.findall(p.read_text()))
    return total


def render_stats_block(
    sim_count: int,
    sorted_domains: list[str],
    total_decls: Optional[int] = None,
    stat_lemma_count: Optional[int] = None,
) -> str:
    """Return the body that goes BETWEEN the sentinel markers.

    Reports three figures so the headline doesn't undersell the
    library:
      * `total_decls`: every theorem/lemma declared in Pythia/.
      * `stat_lemma_count`: theorems registered into the `pythia`
        tactic cascade via `@[stat_lemma]`.
      * `sim_count`: cross-domain theorems with both Lean proof AND
        Python sim runner (PBT + sweep + mutation testing).

    Earlier prose said "N cross-domain theorems" with no qualifier,
    which read as the library size and undersold the surface by 16x.
    """
    n_domains = len(sorted_domains)
    domain_csv = ", ".join(sorted_domains)
    lines = ["**Coverage**:"]
    if total_decls is not None:
        lines.append(f"- {total_decls} theorem/lemma declarations in `Pythia/`")
    if stat_lemma_count is not None:
        lines.append(
            f"- {stat_lemma_count} `@[stat_lemma]`-tagged theorems "
            f"in the `pythia` tactic cascade"
        )
    lines.append(
        f"- {sim_count} cross-domain theorems with Lean proof + Python "
        f"sim runner across {n_domains} domains "
        f"({domain_csv})"
    )
    lines.append("")
    lines.append(
        "Auto-tracked from "
        "[`tools/sim/theorem_manifest.py`](tools/sim/theorem_manifest.py) "
        "and the `Pythia/` source tree; regenerate via "
        "`python3 tools/refresh_readme_stats.py`."
    )
    return "\n".join(lines)


def rewrite_block(
    readme_text: str,
    sim_count: int,
    sorted_domains: list[str],
    total_decls: Optional[int] = None,
    stat_lemma_count: Optional[int] = None,
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
    body = render_stats_block(
        sim_count, sorted(sorted_domains),
        total_decls=total_decls,
        stat_lemma_count=stat_lemma_count,
    )
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
    sim_count = len(manifest)
    sorted_domains = sorted(set(doms))
    total_decls = count_pythia_decls()
    stat_lemma_count = count_stat_lemmas()
    current = readme_path.read_text()
    try:
        rewritten = rewrite_block(
            current, sim_count, sorted_domains,
            total_decls=total_decls,
            stat_lemma_count=stat_lemma_count,
        )
    except ValueError as e:
        print(f"refresh_readme_stats: {e}", file=sys.stderr)
        return 1

    summary = (
        f"{total_decls} total decls / "
        f"{stat_lemma_count} @[stat_lemma] / "
        f"{sim_count} sim-covered across {len(sorted_domains)} domains"
    )
    if rewritten == current:
        print(f"README stats block is already in sync ({summary}).")
        return 0

    if args.check:
        print(
            f"README stats block is STALE. Live values: {summary}. "
            f"Run `python3 tools/refresh_readme_stats.py` to fix.",
            file=sys.stderr,
        )
        return 1

    readme_path.write_text(rewritten)
    print(f"README stats block updated: {summary}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
