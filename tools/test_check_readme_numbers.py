"""Pytest gate: README.md numeric claims must match repo reality.

Wraps `tools/check_readme_numbers.py` so the existing pytest suite
(which already runs the markdown-doctest gate) also enforces README
number-drift. Run as part of the regular `pytest` or via
`python3 -m pytest tools/test_check_readme_numbers.py`.

The check is fast (filesystem grep + a small AST scan), well under
1 sec even on a cold cache. Intended to run on every CI build.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Allow running this test from `pytest tools/test_check_readme_numbers.py`
# regardless of where pytest is invoked.
TOOLS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS_DIR))

from check_readme_numbers import (  # noqa: E402
    parse_readme_claims,
    compute_truth,
    compare,
    README,
)


def test_readme_numeric_claims_match_repo() -> None:
    """Every numeric claim in README.md must match repo reality.

    If this fails, either:
      * Update README.md to match (the repo grew).
      * Investigate why your code change made the repo disagree
        with the README (the change was probably non-trivial and
        deserves narrative + numeric updates in the same PR).
      * Run `python3 tools/check_readme_numbers.py --verbose` to
        see all values.
    """
    text = README.read_text()
    claims = parse_readme_claims(text)
    truth = compute_truth()
    diffs = compare(claims, truth)

    if diffs:
        lines = ["README numeric claims do not match repo:"]
        for key, claimed, actual in diffs:
            lines.append(f"  {key}")
            lines.append(f"    README claims: {claimed}")
            lines.append(f"    Repo reality:  {actual}")
        lines.append("")
        lines.append("Run `python3 tools/check_readme_numbers.py --verbose`")
        lines.append("to see all values.")
        pytest.fail("\n".join(lines))


def test_readme_at_least_one_claim_extracted() -> None:
    """Sanity gate: if regex parsing breaks, the test above would
    silently pass (zero diffs against zero claims). Fail loud here
    if extraction returns nothing.
    """
    text = README.read_text()
    claims = parse_readme_claims(text)
    assert claims, (
        "no numeric claims extracted from README.md — the regex parsing "
        "in check_readme_numbers.py probably broke. Investigate before "
        "trusting the test_readme_numeric_claims_match_repo gate."
    )
