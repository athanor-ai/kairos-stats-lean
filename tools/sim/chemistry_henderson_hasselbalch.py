"""Henderson-Hasselbalch buffer pH monotonicity: empirical companion.

Lean side (`Pythia/Chemistry/HendersonHasselbalch.lean::hh_monotone_in_ratio`)
proves: for all pKa and 0 < r1 <= r2, hhPH(pKa, r1) <= hhPH(pKa, r2),
where hhPH(pKa, ratio) = pKa + log10(ratio).

This module verifies the formal monotonicity bound numerically across
realistic parameter ranges, then runs a mutation harness to confirm the
test set is not passing vacuously.

Run:
    python -m tools.sim.chemistry_henderson_hasselbalch

Or via pytest:
    pytest tools/sim/chemistry_henderson_hasselbalch.py
"""
from __future__ import annotations

import math

from tools.sim.harness import Mutation, Strategy, floats, run_harness


def hh_monotone_spec(pKa: float, r1: float, r2: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True iff hhPH(pKa, lo) <= hhPH(pKa, hi), where lo = min(r1, r2)
    and hi = max(r1, r2). Always True for valid (r1, r2 > 0) pairs.
    """
    lo, hi = sorted([r1, r2])
    return pKa + math.log10(lo) <= pKa + math.log10(hi)


def _reverse_inequality(pKa: float, r1: float, r2: float) -> bool:
    """Claim hi <= lo instead of lo <= hi. Fails when r1 != r2."""
    lo, hi = sorted([r1, r2])
    return pKa + math.log10(hi) <= pKa + math.log10(lo)


def _negate_log(pKa: float, r1: float, r2: float) -> bool:
    """Negate both logs. The inequality reverses for lo < hi, so this fails."""
    lo, hi = sorted([r1, r2])
    return pKa - math.log10(lo) <= pKa - math.log10(hi)


def _offset_only_one_side(pKa: float, r1: float, r2: float) -> bool:
    """Scale the right-hand side by 0.1. Fails when pKa is large or logs differ."""
    lo, hi = sorted([r1, r2])
    return pKa + math.log10(lo) <= 0.1 * (pKa + math.log10(hi))


# Realistic parameter ranges:
#   pKa   : across the chemical scale (0 to 14 covers virtually all weak acids)
#   r1,r2 : base-to-acid ratio [A-]/[HA], three orders of magnitude in each direction
STRATEGY = Strategy(
    pKa=floats(0.0, 14.0),
    r1=floats(1e-3, 1e3, log_scale=True),
    r2=floats(1e-3, 1e3, log_scale=True),
)

MUTATIONS = (
    Mutation(name="reverse_inequality", spec=_reverse_inequality),
    Mutation(name="negate_log", spec=_negate_log),
    Mutation(name="offset_only_one_side", spec=_offset_only_one_side),
)


def main() -> int:
    result = run_harness(
        name="chemistry.hh_monotone_in_ratio",
        spec=hh_monotone_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=8,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_hh_monotone_in_ratio() -> None:
    result = run_harness(
        name="chemistry.hh_monotone_in_ratio",
        spec=hh_monotone_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=8,
        mutations=MUTATIONS,
    )
    assert result.pbt_passed, (
        f"PBT failed at {result.first_pbt_failure}"
    )
    assert result.sweep_passed, (
        f"sweep failed at {result.first_sweep_failure}"
    )
    assert not result.mutations_missed, (
        f"vacuous-test risk: mutations missed = {result.mutations_missed}"
    )


if __name__ == "__main__":
    import sys
    sys.exit(main())
