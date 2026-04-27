"""CI test: every TheoremEntry has a valid, non-empty drafter field.

Gate added in ATH-779 to enforce the paper claim (AI4MATH 2026 §3,
"Drafter swarm and the audit pipeline") that per-theorem drafter
attribution is tracked in the manifest.

The :data:`ALLOWED_DRAFTERS` set is now imported from
``tools.sim.theorem_manifest`` so the manifest's
``__post_init__`` validation and these tests cannot drift. The
``__post_init__`` check raises ``ValueError`` at construction time
on a bad value — failing earlier and louder than waiting for
pytest. These tests exist as a defence-in-depth layer: they catch
any entry that escaped construction (e.g., loaded from JSON) and
report aggregate counts in the CI log.
"""
from __future__ import annotations

from collections import Counter

import pytest

from tools.sim.theorem_manifest import (
    ALLOWED_DRAFTERS,
    MANIFEST,
    TheoremEntry,
)

# Set to the actual count after backfill. If new entries are added with
# drafter="unknown" and this number is exceeded, the test fails — that is
# intentional; the author must set a real drafter value.
MAX_UNKNOWN_COUNT = 0


def test_every_entry_has_nonempty_drafter() -> None:
    """All manifest entries must have a non-empty drafter string."""
    missing = [e.name for e in MANIFEST if not e.drafter]
    assert not missing, f"Entries with empty drafter: {missing}"


def test_all_drafters_in_allowed_set() -> None:
    """Every drafter value must be one of the allowed identifiers.

    Defence-in-depth: ``TheoremEntry.__post_init__`` already raises
    on a bad value at construction. This test catches any case
    where an entry slips past (e.g., constructed via reflection or
    JSON deserialization in a future code path).
    """
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


# ── Construction-time validation tests (post_init) ───────────────────


class TestPostInitValidation:
    """The dataclass ``__post_init__`` raises ``ValueError`` on a bad
    drafter at construction time. These tests pin that behaviour so
    a future refactor that drops the validation breaks CI."""

    def _kwargs(self, **overrides: object) -> dict[str, object]:
        """Minimal valid kwargs for TheoremEntry; tests override one
        field to probe a specific validation rule."""
        base = dict(
            domain="economics",
            name="test_theorem",
            lean_path="Pythia/Test.lean",
            lean_theorem="Pythia.Test.thm",
            sim_path="tools/sim/test.py",
            sim_test="test_thm",
            mathlib_status="novel",
            drafter="sonnet",
        )
        base.update(overrides)
        return base

    def test_accepts_valid_drafter(self) -> None:
        for name in ALLOWED_DRAFTERS:
            entry = TheoremEntry(**self._kwargs(drafter=name))  # type: ignore[arg-type]
            assert entry.drafter == name

    def test_rejects_unknown_drafter_id(self) -> None:
        with pytest.raises(ValueError, match="drafter must be one of"):
            TheoremEntry(**self._kwargs(drafter="claude-sonnet-4-6"))  # type: ignore[arg-type]

    def test_rejects_empty_drafter(self) -> None:
        with pytest.raises(ValueError, match="drafter must be one of"):
            TheoremEntry(**self._kwargs(drafter=""))  # type: ignore[arg-type]

    def test_rejects_capitalised_drafter(self) -> None:
        """Lowercase is the convention (per CLAUDE.md)."""
        with pytest.raises(ValueError, match="drafter must be one of"):
            TheoremEntry(**self._kwargs(drafter="Sonnet"))  # type: ignore[arg-type]

    def test_rejects_invalid_mathlib_status(self) -> None:
        """Defence-in-depth: post_init also validates mathlib_status."""
        with pytest.raises(ValueError, match="mathlib_status"):
            TheoremEntry(**self._kwargs(mathlib_status="invented"))  # type: ignore[arg-type]

    def test_default_drafter_is_unknown(self) -> None:
        """Backward compat: omitting ``drafter=...`` defaults to
        ``"unknown"`` (the audit-time fallback). New entries should
        always set it explicitly, but legacy code that constructs
        TheoremEntry without it must still work."""
        kwargs = self._kwargs()
        kwargs.pop("drafter")
        entry = TheoremEntry(**kwargs)  # type: ignore[arg-type]
        assert entry.drafter == "unknown"
