"""CI test: every TheoremEntry has a valid, non-empty drafter field.

Gate added in ATH-779 to enforce the paper claim (AI4MATH 2026 §3,
"Drafter swarm and the audit pipeline") that per-theorem drafter
attribution is tracked in the manifest. The max_unknown_count ceiling
is set to the actual count at backfill time (0) so future drift is caught
immediately.
"""
from __future__ import annotations

from collections import Counter

import pytest

from tools.sim.theorem_manifest import MANIFEST, TheoremEntry

ALLOWED_DRAFTERS = frozenset({"aristotle", "dspv2", "sonnet", "opus", "human", "unknown"})

# Set to the actual count after backfill. If new entries are added with
# drafter="unknown" and this number is exceeded, the test fails — that is
# intentional; the author must set a real drafter value.
MAX_UNKNOWN_COUNT = 0


def test_every_entry_has_nonempty_drafter() -> None:
    """All manifest entries must have a non-empty drafter string."""
    missing = [e.name for e in MANIFEST if not e.drafter]
    assert not missing, f"Entries with empty drafter: {missing}"


def test_all_drafters_in_allowed_set() -> None:
    """Every drafter value must be one of the allowed identifiers."""
    bad = [(e.name, e.drafter) for e in MANIFEST if e.drafter not in ALLOWED_DRAFTERS]
    assert not bad, (
        f"Entries with disallowed drafter values: {bad}. "
        f"Allowed: {sorted(ALLOWED_DRAFTERS)}"
    )


def test_unknown_count_within_ceiling() -> None:
    """The number of 'unknown' entries must not exceed the backfill ceiling.

    This catches new theorems added without attribution research.
    To raise the ceiling intentionally, update MAX_UNKNOWN_COUNT above
    and leave a comment explaining why the entry cannot be attributed.
    """
    unknown_entries = [e.name for e in MANIFEST if e.drafter == "unknown"]
    assert len(unknown_entries) <= MAX_UNKNOWN_COUNT, (
        f"Found {len(unknown_entries)} 'unknown' drafter entries (ceiling={MAX_UNKNOWN_COUNT}): "
        f"{unknown_entries}. "
        "Backfill from git log / PR bodies or set drafter='human' / raise MAX_UNKNOWN_COUNT "
        "with an explanatory comment."
    )


def test_drafter_counts_summary(capsys: pytest.CaptureFixture[str]) -> None:
    """Informational: print per-drafter counts so CI logs are self-documenting."""
    counts = Counter(e.drafter for e in MANIFEST)
    capsys.readouterr()  # flush any prior output
    print("\nPer-drafter theorem counts:")
    for drafter in sorted(ALLOWED_DRAFTERS):
        n = counts.get(drafter, 0)
        if n:
            print(f"  {drafter}: {n}")
    print(f"  total: {len(MANIFEST)}")
