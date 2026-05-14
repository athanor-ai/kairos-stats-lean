"""Put-call parity (algebraic + discounted forms): empirical companion.

Lean side (`Pythia/Finance/PutCallParity.lean`):
  * `put_call_payoff_identity` —
      max(S - K, 0) - max(K - S, 0) = S - K
  * `put_call_parity_discounted` —
      callPayoff S K T r - putPayoff S K T r = (S - K) * exp(-rT)

This module verifies both identities numerically across realistic
parameter ranges (positive spot / strike / time-to-expiry / non-zero
rate including negative-rate regimes) and runs a mutation harness to
confirm the test set is not passing vacuously.

Run:
    python -m tools.sim.finance_put_call_parity

Or via pytest:
    pytest tools/sim/finance_put_call_parity.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def put_call_payoff_identity_spec(S: float, K: float) -> bool:
    """Algebraic kernel: max(S-K, 0) - max(K-S, 0) = S - K (exact)."""
    lhs = max(S - K, 0.0) - max(K - S, 0.0)
    rhs = S - K
    return math.isclose(lhs, rhs, abs_tol=1e-12, rel_tol=1e-9)


def put_call_parity_discounted_spec(S: float, K: float, T: float, r: float) -> bool:
    """Discounted form:
        callPayoff - putPayoff = (S - K) * exp(-rT)
    with callPayoff = max(S-K, 0) * exp(-rT),
         putPayoff  = max(K-S, 0) * exp(-rT)."""
    discount = math.exp(-r * T)
    call = max(S - K, 0.0) * discount
    put = max(K - S, 0.0) * discount
    lhs = call - put
    rhs = (S - K) * discount
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Mutations — perturbations that should FAIL the spec on >= min_failure_rate
# ============================================================================


def _identity_drop_max(S: float, K: float) -> bool:
    """Drops both max guards: (S - K) - (K - S) = 2(S - K) ≠ S - K
    (fails whenever S ≠ K)."""
    lhs = (S - K) - (K - S)
    rhs = S - K
    return math.isclose(lhs, rhs, abs_tol=1e-12, rel_tol=1e-9)


def _identity_swap_signs(S: float, K: float) -> bool:
    """Swaps the sign of the second max term:
        max(S-K, 0) + max(K-S, 0) = |S - K| ≠ S - K
    (fails whenever S < K, producing |S-K| = K-S ≠ S-K)."""
    lhs = max(S - K, 0.0) + max(K - S, 0.0)
    rhs = S - K
    return math.isclose(lhs, rhs, abs_tol=1e-12, rel_tol=1e-9)


def _discount_drop_factor(S: float, K: float, T: float, r: float) -> bool:
    """Drops the exp(-rT) discount on the RHS:
        callPayoff - putPayoff = S - K
    Fails whenever rT ≠ 0 (and S ≠ K)."""
    discount = math.exp(-r * T)
    call = max(S - K, 0.0) * discount
    put = max(K - S, 0.0) * discount
    lhs = call - put
    rhs = S - K  # missing * discount
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _discount_wrong_sign(S: float, K: float, T: float, r: float) -> bool:
    """Wrong-sign in the discount exponent: exp(+rT) instead of exp(-rT).
    Fails whenever rT ≠ 0 because the LHS uses one factor and the RHS
    uses its inverse."""
    discount_correct = math.exp(-r * T)
    discount_wrong = math.exp(r * T)
    call = max(S - K, 0.0) * discount_correct
    put = max(K - S, 0.0) * discount_correct
    lhs = call - put
    rhs = (S - K) * discount_wrong
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Strategies — parameter-range distributions for property-based testing
# ============================================================================


# Spot prices typically in [0.01, 10_000] for equities; allow wider for FX.
_strategy_identity = Strategy(
    S=floats(lo=-1e4, hi=1e4),
    K=floats(lo=-1e4, hi=1e4),
)


# Discounted form: include negative-rate regime (post-2008 markets) +
# realistic time-to-expiry [0, 10] years.
_strategy_discounted = Strategy(
    S=floats(lo=0.01, hi=1e4),
    K=floats(lo=0.01, hi=1e4),
    T=floats(lo=0.0, hi=10.0),
    r=floats(lo=-0.05, hi=0.20),
)


# ============================================================================
# Test entry-points
# ============================================================================


def test_put_call_payoff_identity():
    result = run_harness(
        name="put_call_payoff_identity",
        spec=put_call_payoff_identity_spec,
        strategy=_strategy_identity,
        mutations=(
            Mutation("drop_max", _identity_drop_max, min_failure_rate=0.30),
            Mutation("swap_signs", _identity_swap_signs, min_failure_rate=0.30),
        ),
    )
    assert result.all_passed, result.summarize()


def test_put_call_parity_discounted():
    result = run_harness(
        name="put_call_parity_discounted",
        spec=put_call_parity_discounted_spec,
        strategy=_strategy_discounted,
        mutations=(
            Mutation("drop_factor", _discount_drop_factor, min_failure_rate=0.50),
            Mutation("wrong_sign", _discount_wrong_sign, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


if __name__ == "__main__":
    test_put_call_payoff_identity()
    test_put_call_parity_discounted()
    print("put-call parity: all property-based and mutation tests passed.")
