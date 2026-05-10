#!/usr/bin/env python3
"""CI gate: every theorem name in lean_citations.py must exist in Pythia.

Greps each cited theorem name against the Pythia source tree.
Any phantom (cited but not defined) fails CI. Structural enforcement
against phantom citations — the system rejects, not the reviewer.

Usage:
    python3 tools/check_lean_citation_phantoms.py [--citations-file PATH]

Exit 0 if all citations map to real theorems.
Exit 1 if any phantom found.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PYTHIA_DIR = REPO_ROOT / "Pythia"


def extract_theorem_names(citations_file: Path) -> list[str]:
    """Extract all theorem_name values from a lean_citations.py file."""
    text = citations_file.read_text()
    return re.findall(r'theorem_name="([^"]+)"', text)


def grep_theorem(name: str) -> bool:
    """Check if a theorem name exists in any .lean file under Pythia/."""
    short = name.split(".")[-1]
    result = subprocess.run(
        ["grep", "-rq", f"theorem {short}\\|def {short}\\|lemma {short}",
         str(PYTHIA_DIR)],
        capture_output=True,
    )
    return result.returncode == 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--citations-file",
        type=Path,
        default=None,
        help="Path to lean_citations.py (auto-detected if not given)",
    )
    args = parser.parse_args()

    citations_file = args.citations_file
    if citations_file is None:
        candidates = list(REPO_ROOT.rglob("lean_citations.py"))
        if not candidates:
            print("No lean_citations.py found — skipping phantom check.")
            return 0
        citations_file = candidates[0]

    names = extract_theorem_names(citations_file)
    if not names:
        print("No theorem citations found — nothing to check.")
        return 0

    phantoms = []
    for name in names:
        if grep_theorem(name):
            print(f"  OK: {name}")
        else:
            print(f"  PHANTOM: {name}")
            phantoms.append(name)

    print(f"\n{len(names)} citations checked, {len(phantoms)} phantoms.")

    if phantoms:
        print("\nFAILED — phantom citations found:")
        for p in phantoms:
            print(f"  {p}")
        print("\nEvery citation must map to a real theorem in Pythia/.")
        print("Either build the theorem or remove the citation.")
        return 1

    print("\nPASSED — zero phantom citations.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
