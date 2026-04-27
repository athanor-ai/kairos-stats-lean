"""Cauchy-Schwarz inequality (two variables): empirical companion.

Lean side (`Pythia/MathlibTags.lean::cauchy_schwarz_two`) proves:
    (a*c + b*d)^2 <= (a^2 + b^2) * (c^2 + d^2)   for all a b c d : Real.

The formal proof is entirely self-contained and uses the discriminant
identity (a*d - b*c)^2 >= 0, which expands directly to give the
inequality. No exotic lemma is borrowed from Mathlib for this 2-variable
form. The retag of the inner-product version `inner_mul_le_norm_mul_norm`
is left for a follow-up batch.

Run:
    python -m tools.sim.mathlib_tags_cauchy_schwarz

Or via pytest:
    pytest tools/sim/mathlib_tags_cauchy_schwarz.py
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


def cauchy_schwarz_two_spec(a: float, b: float, c: float, d: float) -> bool:
    """The 2-variable Cauchy-Schwarz theorem evaluated numerically.

    Returns True when (a*c + b*d)**2 <= (a**2 + b**2)*(c**2 + d**2),
    with a slack of 1e-9 to absorb floating-point noise at the equality
    case (parallel vectors, e.g. a/b == c/d).
    """
    lhs = (a * c + b * d) ** 2
    rhs = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)
    return lhs <= rhs + 1e-9


# Mutations: each deliberately perturbs the spec. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _swap_inequality(a: float, b: float, c: float, d: float) -> bool:
    """Flipped inequality: (a*c + b*d)**2 > (a**2 + b**2)*(c**2 + d**2).
    True only at equality (parallel vectors), probability zero for
    continuous draws. Fails almost surely."""
    lhs = (a * c + b * d) ** 2
    rhs = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)
    return lhs > rhs + 1e-9


def _drop_squares_lhs(a: float, b: float, c: float, d: float) -> bool:
    """Overly tight: (a*c + b*d)**2 <= 0.5 * (a**2 + b**2)*(c**2 + d**2).
    Fails when vectors are nearly parallel (CS near tight), e.g. a==c,
    b==d, where LHS == RHS, well above 0.5*RHS for non-zero inputs."""
    lhs = (a * c + b * d) ** 2
    rhs = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)
    return lhs <= 0.5 * rhs + 1e-9


def _drop_one_factor(a: float, b: float, c: float, d: float) -> bool:
    """Missing second factor: (a*c + b*d)**2 <= (a**2 + b**2).
    Fails whenever c or d is large in magnitude, making the true RHS
    much bigger than (a**2 + b**2), so the bound is violated."""
    lhs = (a * c + b * d) ** 2
    rhs = a ** 2 + b ** 2
    return lhs <= rhs + 1e-9


# Parameter ranges: uniform in [-100, 100] on each axis.
# Broad real-valued range covering negative values, zero, and large magnitudes.
STRATEGY = Strategy(
    a=floats(-100.0, 100.0),
    b=floats(-100.0, 100.0),
    c=floats(-100.0, 100.0),
    d=floats(-100.0, 100.0),
)

MUTATIONS = (
    Mutation(name="swap_inequality", spec=_swap_inequality),
    Mutation(name="drop_squares_lhs", spec=_drop_squares_lhs),
    Mutation(name="drop_one_factor", spec=_drop_one_factor),
)


def main() -> int:
    result = run_harness(
        name="mathlib_tags.cauchy_schwarz_two",
        spec=cauchy_schwarz_two_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_cauchy_schwarz_two() -> None:
    """pytest hook: runs a shorter harness and asserts all checks pass."""
    result = run_harness(
        name="mathlib_tags.cauchy_schwarz_two",
        spec=cauchy_schwarz_two_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=5,
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
