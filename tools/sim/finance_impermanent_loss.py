"""Impermanent loss (DEX AMM constant-product): empirical companion.

Lean side (`Pythia/Finance/ImpermanentLoss.lean`):
  * `impermanentLoss r := (2·√r)/(1+r) - 1`
  * `impermanentLoss_at_one : IL(1) = 0`
  * `impermanentLoss_nonpos : 0 < r → IL(r) ≤ 0`

This module verifies the IL formula numerically across realistic
price-ratio ranges and runs a mutation harness to confirm the test
set is not vacuous.

Run:
    python3 -m tools.sim.finance_impermanent_loss

Or via pytest:
    pytest tools/sim/finance_impermanent_loss.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def impermanent_loss(r: float) -> float:
    return (2 * math.sqrt(r)) / (1 + r) - 1


def impermanent_loss_nonpos_spec(r: float) -> bool:
    """`impermanentLoss r ≤ 0` for r > 0, with the algebraic identity
    `(1 + r) · (IL + 1) = 2 · √r` (algebraic form of the closed-form
    definition) — verifies BOTH non-positivity AND closed-form
    correctness."""
    if r <= 0:
        return True
    il = impermanent_loss(r)
    if il > 1e-9:
        return False
    # Closed-form consistency: (1+r) · (IL + 1) = 2 · √r
    return math.isclose((1 + r) * (il + 1), 2 * math.sqrt(r),
                        abs_tol=1e-9, rel_tol=1e-9)


def impermanent_loss_at_one_spec(r: float) -> bool:
    """At r=1, IL is zero (within FP tolerance)."""
    if not math.isclose(r, 1.0, abs_tol=1e-12, rel_tol=1e-12):
        return True  # vacuously OK
    return math.isclose(impermanent_loss(r), 0.0, abs_tol=1e-12, rel_tol=1e-9)


# ============================================================================
# Mutations
# ============================================================================


def _drop_sqrt(r: float) -> bool:
    """Uses r instead of √r in the numerator. Fails the closed-form
    identity (1+r)·(IL+1) = 2·√r whenever r ≠ 1."""
    if r <= 0:
        return True
    mutant = (2 * r) / (1 + r) - 1
    if mutant > 1e-9:
        return False
    return math.isclose((1 + r) * (mutant + 1), 2 * math.sqrt(r),
                        abs_tol=1e-9, rel_tol=1e-9)


def _wrong_sign_numerator(r: float) -> bool:
    """Negates the numerator: -2√r/(1+r) - 1.
    The mutant fails the closed-form check
    `(1+r)·(IL+1) = 2·√r` whenever r > 0."""
    if r <= 0:
        return True
    mutant = (-2 * math.sqrt(r)) / (1 + r) - 1
    if mutant > 1e-9:
        return False
    return math.isclose((1 + r) * (mutant + 1), 2 * math.sqrt(r),
                        abs_tol=1e-9, rel_tol=1e-9)


def _drop_minus_one(r: float) -> bool:
    """Drops the -1 at the end: (2√r)/(1+r) instead of -1.
    The mutant is strictly positive, failing the ≤ 0 check."""
    if r <= 0:
        return True
    mutant = (2 * math.sqrt(r)) / (1 + r)
    if mutant > 1e-9:
        return False
    return math.isclose((1 + r) * (mutant + 1), 2 * math.sqrt(r),
                        abs_tol=1e-9, rel_tol=1e-9)


def _quadratic_denominator(r: float) -> bool:
    """Wrong denominator: 1 + r² instead of 1 + r.
    Fails the closed-form identity (1+r)·(IL+1) = 2·√r for r ≠ 1."""
    if r <= 0:
        return True
    mutant = (2 * math.sqrt(r)) / (1 + r * r) - 1
    if mutant > 1e-9:
        return False
    return math.isclose((1 + r) * (mutant + 1), 2 * math.sqrt(r),
                        abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Strategies
# ============================================================================


_strategy_general = Strategy(
    r=floats(lo=1e-4, hi=1e4, log_scale=True),
)


_strategy_near_one = Strategy(
    r=floats(lo=0.9, hi=1.1),
)


# ============================================================================
# Tests
# ============================================================================


def test_impermanent_loss_nonpos():
    result = run_harness(
        name="impermanent_loss_nonpos",
        spec=impermanent_loss_nonpos_spec,
        strategy=_strategy_general,
        mutations=(
            Mutation("drop_sqrt", _drop_sqrt, min_failure_rate=0.30),
            Mutation("drop_minus_one", _drop_minus_one, min_failure_rate=0.30),
            Mutation("quadratic_denominator", _quadratic_denominator, min_failure_rate=0.30),
            Mutation("wrong_sign_numerator", _wrong_sign_numerator, min_failure_rate=0.05),
        ),
    )
    assert result.all_passed, result.summarize()


if __name__ == "__main__":
    test_impermanent_loss_nonpos()
    print("impermanent_loss: PBT + 4 mutation tests passed.")
