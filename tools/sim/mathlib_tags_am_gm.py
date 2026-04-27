"""Arithmetic-Geometric Mean (two variables): empirical companion.

Lean side (`Pythia/MathlibTags.lean::am_gm_two`) proves:
    sqrt(a * b) <= (a + b) / 2   for all a, b >= 0.

The formal proof lives in Mathlib via `Real.mul_self_sqrt` and
`Real.sqrt_mul`; pythia adds the registry entry (`@[stat_lemma]`)
and this empirical layer. This module verifies the bound numerically
across a wide parameter range and runs a mutation harness to confirm
the test set is not passing vacuously.

Run:
    python -m tools.sim.mathlib_tags_am_gm

Or via pytest:
    pytest tools/sim/mathlib_tags_am_gm.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    le,
    run_harness,
)


def am_gm_two_spec(a: float, b: float) -> bool:
    """The AM-GM theorem itself, evaluated numerically.

    Returns True when sqrt(a * b) <= (a + b) / 2, which the Lean
    theorem guarantees for all a, b >= 0.
    Uses `le(..., atol=1e-9)` to absorb floating-point noise at
    the equality case (a == b).
    """
    return le(math.sqrt(a * b), (a + b) / 2, atol=1e-9)


# Mutations: each deliberately perturbs the spec. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _swap_inequality(a: float, b: float) -> bool:
    """Flipped inequality: sqrt(a*b) > (a+b)/2.
    True only when a==b (equality), which happens with probability
    zero for continuous draws. Fails almost surely."""
    return math.sqrt(a * b) > (a + b) / 2


def _off_by_factor_5(a: float, b: float) -> bool:
    """Overly tight divisor: sqrt(a*b) <= (a+b)/5.
    Fails whenever a and b are close in magnitude (ratio near 1)
    because then sqrt(ab) is close to (a+b)/2, well above (a+b)/5."""
    return math.sqrt(a * b) <= (a + b) / 5


def _wrong_mean(a: float, b: float) -> bool:
    """Overly tight divisor: sqrt(a*b) <= (a+b)/3.
    Fails whenever the geometric mean exceeds one-third of the sum,
    which happens for the vast majority of draws (roughly 85 percent
    of uniform samples in [0, 1000]^2) because the true bound is
    (a+b)/2, not (a+b)/3."""
    return math.sqrt(a * b) <= (a + b) / 3


# Parameter ranges: uniform in [0, 1000] x [0, 1000].
# Wide enough to exercise the full inequality curve.
STRATEGY = Strategy(
    a=floats(0.0, 1000.0),
    b=floats(0.0, 1000.0),
)

MUTATIONS = (
    Mutation(name="swap_inequality", spec=_swap_inequality),
    Mutation(name="off_by_factor_5", spec=_off_by_factor_5),
    Mutation(name="wrong_mean", spec=_wrong_mean),
)


def main() -> int:
    result = run_harness(
        name="mathlib_tags.am_gm_two",
        spec=am_gm_two_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_am_gm_two() -> None:
    """pytest hook: runs a shorter harness and asserts all checks pass."""
    result = run_harness(
        name="mathlib_tags.am_gm_two",
        spec=am_gm_two_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=15,
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
