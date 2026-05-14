"""√t volatility-scaling rule: empirical companion.

Lean side (`Pythia/Finance/VolatilityScaling.lean`):
  * `volatilityScale σ_d n := σ_d · √n`
  * `volatilityScale_zero_horizon / unit_horizon / monotone / squared`

Run:
    python3 -m tools.sim.finance_volatility_scaling

Or via pytest:
    pytest tools/sim/finance_volatility_scaling.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def volatility_scale(sigma_d: float, n: float) -> float:
    return sigma_d * math.sqrt(n)


def volatility_scale_squared_spec(sigma_d: float, n: float) -> bool:
    """(σ_d · √n)² = σ_d² · n  for n ≥ 0."""
    if n < 0:
        return True
    lhs = volatility_scale(sigma_d, n) ** 2
    rhs = sigma_d * sigma_d * n
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def volatility_scale_unit_horizon_spec(sigma_d: float) -> bool:
    return math.isclose(volatility_scale(sigma_d, 1.0), sigma_d,
                        abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Mutations
# ============================================================================


def _drop_sqrt(sigma_d: float, n: float) -> bool:
    """Uses n instead of √n. Then (σ_d · n)² = σ_d² · n² ≠ σ_d² · n."""
    if n < 0:
        return True
    lhs = (sigma_d * n) ** 2
    rhs = sigma_d * sigma_d * n
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _cube_not_square(sigma_d: float, n: float) -> bool:
    """Uses (σ_d · √n)³ instead of squared. Fails wide."""
    if n < 0:
        return True
    lhs = (sigma_d * math.sqrt(n)) ** 3
    rhs = sigma_d * sigma_d * n
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _wrong_rhs(sigma_d: float, n: float) -> bool:
    """Wrong RHS: σ_d² · n² (variance scales quadratically not linearly)."""
    if n < 0:
        return True
    lhs = volatility_scale(sigma_d, n) ** 2
    rhs = sigma_d * sigma_d * n * n  # quadratic in n (wrong)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _additive_not_multiplicative(sigma_d: float, n: float) -> bool:
    """Wrong scaling: σ_d + √n instead of σ_d · √n."""
    if n < 0:
        return True
    lhs = (sigma_d + math.sqrt(n)) ** 2
    rhs = sigma_d * sigma_d * n
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Strategies
# ============================================================================


_strategy = Strategy(
    sigma_d=floats(lo=0.001, hi=2.0),
    n=floats(lo=0.0, hi=10000.0),
)


_strategy_unit = Strategy(
    sigma_d=floats(lo=0.001, hi=2.0),
)


# ============================================================================
# Tests
# ============================================================================


def test_volatility_scale_squared():
    result = run_harness(
        name="volatility_scale_squared",
        spec=volatility_scale_squared_spec,
        strategy=_strategy,
        mutations=(
            Mutation("drop_sqrt", _drop_sqrt, min_failure_rate=0.50),
            Mutation("cube_not_square", _cube_not_square, min_failure_rate=0.50),
            Mutation("wrong_rhs_quadratic", _wrong_rhs, min_failure_rate=0.50),
            Mutation("additive_not_multiplicative", _additive_not_multiplicative, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


def test_volatility_scale_unit_horizon():
    result = run_harness(
        name="volatility_scale_unit_horizon",
        spec=volatility_scale_unit_horizon_spec,
        strategy=_strategy_unit,
    )
    assert result.all_passed, result.summarize()


if __name__ == "__main__":
    test_volatility_scale_squared()
    test_volatility_scale_unit_horizon()
    print("volatility_scaling: PBT + 4 mutation tests passed.")
