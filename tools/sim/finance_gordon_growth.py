"""Gordon growth model (constant-dividend-growth equity valuation): empirical companion.

Lean side (`Pythia/Finance/GordonGrowth.lean`):
  * `gordonGrowthPrice D₁ r g := D₁ / (r − g)`
  * zero-growth → perpetuity, linear in D₁, scale-invariance in D₁

Run:
    python3 -m tools.sim.finance_gordon_growth

Or via pytest:
    pytest tools/sim/finance_gordon_growth.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def gordon_price(D1: float, r: float, g: float) -> float:
    return D1 / (r - g)


def gordon_zero_growth_spec(D1: float, r: float) -> bool:
    """At g=0: P = D₁ / r (the simple perpetuity formula)."""
    lhs = gordon_price(D1, r, 0.0)
    rhs = D1 / r
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def gordon_scale_D_spec(D1: float, alpha: float, r: float, g: float) -> bool:
    """Scaling D₁ by α scales price by α."""
    lhs = gordon_price(alpha * D1, r, g)
    rhs = alpha * gordon_price(D1, r, g)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Mutations
# ============================================================================


def _zero_growth_drop_division(D1: float, r: float) -> bool:
    """Wrong: claims P(D, r, 0) = D · r (multiplied instead of divided)."""
    lhs = gordon_price(D1, r, 0.0)
    rhs = D1 * r
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _zero_growth_subtract_one(D1: float, r: float) -> bool:
    """Wrong: claims P(D, r, 0) = D / (r - 1)."""
    lhs = gordon_price(D1, r, 0.0)
    rhs = D1 / (r - 1.0)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _scale_D_wrong_factor(D1: float, alpha: float, r: float, g: float) -> bool:
    """Wrong: claims (α·D)/((r-g)) scales by α² (off by α)."""
    lhs = gordon_price(alpha * D1, r, g)
    rhs = (alpha ** 2) * gordon_price(D1, r, g)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _gordon_wrong_denominator(D1: float, r: float, g: float) -> bool:
    """Wrong: uses D / (r + g) instead of D / (r - g). Fails for g ≠ 0."""
    mutant = D1 / (r + g)
    correct = gordon_price(D1, r, g)
    return math.isclose(mutant, correct, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Strategies
# ============================================================================


_strategy_zero_growth = Strategy(
    D1=floats(lo=0.1, hi=10.0),
    r=floats(lo=0.02, hi=0.20),
)


_strategy_scale = Strategy(
    D1=floats(lo=0.1, hi=10.0),
    alpha=floats(lo=0.5, hi=3.0),
    r=floats(lo=0.05, hi=0.20),
    g=floats(lo=0.0, hi=0.04),  # g < r
)


_strategy_general = Strategy(
    D1=floats(lo=0.1, hi=10.0),
    r=floats(lo=0.05, hi=0.20),
    g=floats(lo=0.01, hi=0.04),  # g < r, both strictly positive so r+g ≠ r-g
)


# ============================================================================
# Tests
# ============================================================================


def test_gordon_zero_growth():
    result = run_harness(
        name="gordon_zero_growth",
        spec=gordon_zero_growth_spec,
        strategy=_strategy_zero_growth,
        mutations=(
            Mutation("drop_division", _zero_growth_drop_division, min_failure_rate=0.50),
            Mutation("subtract_one", _zero_growth_subtract_one, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


def test_gordon_scale_D():
    result = run_harness(
        name="gordon_scale_D",
        spec=gordon_scale_D_spec,
        strategy=_strategy_scale,
        mutations=(
            Mutation("wrong_factor", _scale_D_wrong_factor, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


def test_gordon_denominator_form():
    """Catch the (r+g) wrong-denominator mutant via the general (D, r, g)
    range. Spec passes trivially (well-formedness) — mutation carries the test."""

    def spec(D1: float, r: float, g: float) -> bool:
        return math.isfinite(gordon_price(D1, r, g))

    result = run_harness(
        name="gordon_denominator_form",
        spec=spec,
        strategy=_strategy_general,
        mutations=(
            Mutation("wrong_denominator", _gordon_wrong_denominator, min_failure_rate=0.50),
        ),
    )
    assert "wrong_denominator" in result.mutations_caught, (
        f"Expected 'wrong_denominator' caught, got "
        f"caught={result.mutations_caught} missed={result.mutations_missed}"
    )


if __name__ == "__main__":
    test_gordon_zero_growth()
    test_gordon_scale_D()
    test_gordon_denominator_form()
    print("gordon_growth: PBT + 4 mutation tests passed.")
