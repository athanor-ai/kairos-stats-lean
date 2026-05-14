"""Forward price for dividend-paying asset: empirical companion.

Lean side (`Pythia/Finance/ForwardPrice.lean`):
  * `forwardPrice S r q T := S * exp((r - q) * T)`
  * `forwardPrice_pos / zero_time / zero_dividend`

Run:
    python3 -m tools.sim.finance_forward_price

Or via pytest:
    pytest tools/sim/finance_forward_price.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def forward_price(S: float, r: float, q: float, T: float) -> float:
    return S * math.exp((r - q) * T)


def forward_price_pos_spec(S: float, r: float, q: float, T: float) -> bool:
    if S <= 0:
        return True
    return forward_price(S, r, q, T) > 0


def forward_price_zero_dividend_spec(S: float, r: float, T: float) -> bool:
    """forwardPrice S r 0 T = S · exp(r·T)."""
    lhs = forward_price(S, r, 0.0, T)
    rhs = S * math.exp(r * T)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def forward_price_zero_time_spec(S: float, r: float, q: float) -> bool:
    """forwardPrice S r q 0 = S."""
    return math.isclose(forward_price(S, r, q, 0.0), S,
                        abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Mutations
# ============================================================================


def _drop_dividend_subtract(S: float, r: float, q: float, T: float) -> bool:
    """Wrong: S·exp((r+q)T) instead of (r-q)T. Fails when q ≠ 0 and T ≠ 0."""
    lhs = S * math.exp((r + q) * T)  # wrong
    rhs = S * math.exp((r - q) * T)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _zero_dividend_doubles_rate(S: float, r: float, T: float) -> bool:
    """Wrong zero_dividend: 2·S·exp(r·T) instead of S·exp(r·T)."""
    lhs = forward_price(S, r, 0.0, T)
    rhs = 2 * S * math.exp(r * T)  # wrong
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _zero_dividend_drops_exp(S: float, r: float, T: float) -> bool:
    """Wrong: forward at q=0 equals S (no rate compounding). Fails for r·T ≠ 0."""
    lhs = forward_price(S, r, 0.0, T)
    rhs = S  # missing exp(r·T)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _zero_time_with_S_squared(S: float, r: float, q: float) -> bool:
    """Wrong zero_time: S² instead of S."""
    lhs = forward_price(S, r, q, 0.0)
    rhs = S * S  # wrong
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Strategies
# ============================================================================


_strategy = Strategy(
    S=floats(lo=0.01, hi=1e4, log_scale=True),
    r=floats(lo=-0.05, hi=0.20),
    q=floats(lo=0.0, hi=0.10),
    T=floats(lo=0.01, hi=10.0),
)


_strategy_zero_dividend = Strategy(
    S=floats(lo=0.01, hi=1e4, log_scale=True),
    r=floats(lo=-0.05, hi=0.20),
    T=floats(lo=0.01, hi=10.0),
)


_strategy_zero_time = Strategy(
    S=floats(lo=0.01, hi=1e4, log_scale=True),
    r=floats(lo=-0.05, hi=0.20),
    q=floats(lo=0.0, hi=0.10),
)


# ============================================================================
# Tests
# ============================================================================


def test_forward_price_pos():
    result = run_harness(
        name="forward_price_pos",
        spec=forward_price_pos_spec,
        strategy=_strategy,
    )
    assert result.all_passed, result.summarize()


def test_forward_price_zero_dividend():
    result = run_harness(
        name="forward_price_zero_dividend",
        spec=forward_price_zero_dividend_spec,
        strategy=_strategy_zero_dividend,
        mutations=(
            Mutation("zero_dividend_doubles_rate", _zero_dividend_doubles_rate, min_failure_rate=0.50),
            Mutation("zero_dividend_drops_exp", _zero_dividend_drops_exp, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


def test_forward_price_zero_time():
    result = run_harness(
        name="forward_price_zero_time",
        spec=forward_price_zero_time_spec,
        strategy=_strategy_zero_time,
        mutations=(
            Mutation("zero_time_with_S_squared", _zero_time_with_S_squared, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


if __name__ == "__main__":
    test_forward_price_pos()
    test_forward_price_zero_dividend()
    test_forward_price_zero_time()
    print("forward_price: PBT + 3 mutation tests passed.")
