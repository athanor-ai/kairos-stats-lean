"""Continuous-compounding discount factor: empirical companion.

Lean side (`Pythia/Finance/DiscountFactor.lean`):
  * `discountFactor r T := exp(-(r * T))`
  * `discountFactor_pos / zero_time / zero_rate / antitone_rate /
    antitone_time / le_one`

Run:
    python3 -m tools.sim.finance_discount_factor

Or via pytest:
    pytest tools/sim/finance_discount_factor.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def discount_factor(r: float, T: float) -> float:
    return math.exp(-(r * T))


def discount_factor_le_one_spec(r: float, T: float) -> bool:
    """For r·T ≥ 0: D(r, T) ≤ 1."""
    if r * T < 0:
        return True
    return discount_factor(r, T) <= 1 + 1e-12


def discount_factor_pos_spec(r: float, T: float) -> bool:
    """D(r, T) > 0 unconditionally."""
    return discount_factor(r, T) > 0


def discount_factor_antitone_rate_spec(T: float, r1: float, r2: float) -> bool:
    """T ≥ 0, r1 ≤ r2 → D(r2, T) ≤ D(r1, T)."""
    if T < 0 or r1 > r2:
        return True
    return discount_factor(r2, T) <= discount_factor(r1, T) + 1e-12


# ============================================================================
# Mutations
# ============================================================================


def _wrong_sign_exponent(r: float, T: float) -> bool:
    """Drops the negative sign: exp(rT) instead of exp(-rT).
    For r·T > 0, mutant > 1 → fails the ≤ 1 test."""
    if r * T < 0:
        return True
    mutant = math.exp(r * T)
    return mutant <= 1 + 1e-12


def _drop_T_in_exponent(r: float, T: float) -> bool:
    """Uses exp(-r) instead of exp(-r·T). Fails when T ≠ 1."""
    if r * T < 0:
        return True
    mutant = math.exp(-r)
    correct = discount_factor(r, T)
    return math.isclose(mutant, correct, abs_tol=1e-9, rel_tol=1e-9)


def _additive_exponent(r: float, T: float) -> bool:
    """Uses exp(-(r + T)) instead of exp(-(r·T)). Wrong dimensional analysis."""
    if r * T < 0:
        return True
    mutant = math.exp(-(r + T))
    correct = discount_factor(r, T)
    return math.isclose(mutant, correct, abs_tol=1e-9, rel_tol=1e-9)


def _antitone_wrong_direction(T: float, r1: float, r2: float) -> bool:
    """Claims D(r1, T) ≤ D(r2, T) — wrong direction (monotone instead
    of antitone)."""
    if T < 0 or r1 > r2:
        return True
    return discount_factor(r1, T) <= discount_factor(r2, T) + 1e-12


# ============================================================================
# Strategies
# ============================================================================


_strategy = Strategy(
    r=floats(lo=-0.05, hi=0.30),
    T=floats(lo=0.01, hi=30.0),
)


_strategy_antitone = Strategy(
    T=floats(lo=0.01, hi=30.0),
    r1=floats(lo=-0.05, hi=0.15),
    r2=floats(lo=0.15, hi=0.50),
)


# ============================================================================
# Tests
# ============================================================================


def test_discount_factor_le_one():
    result = run_harness(
        name="discount_factor_le_one",
        spec=discount_factor_le_one_spec,
        strategy=_strategy,
        mutations=(
            Mutation("wrong_sign_exponent", _wrong_sign_exponent, min_failure_rate=0.50),
            Mutation("drop_T_in_exponent", _drop_T_in_exponent, min_failure_rate=0.50),
            Mutation("additive_exponent", _additive_exponent, min_failure_rate=0.30),
        ),
    )
    assert result.all_passed, result.summarize()


def test_discount_factor_antitone_rate():
    result = run_harness(
        name="discount_factor_antitone_rate",
        spec=discount_factor_antitone_rate_spec,
        strategy=_strategy_antitone,
        mutations=(
            Mutation("antitone_wrong_direction", _antitone_wrong_direction, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


if __name__ == "__main__":
    test_discount_factor_le_one()
    test_discount_factor_antitone_rate()
    print("discount_factor: PBT + 4 mutation tests passed.")
