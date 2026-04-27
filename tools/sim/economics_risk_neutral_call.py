"""Risk-neutral European call option non-negativity: empirical companion.

Lean side (`Pythia/Economics/RiskNeutralCall.lean::risk_neutral_call_nonneg`)
proves: `max(S - K, 0) * exp(-r * T) >= 0` for any S, K, r and T >= 0.

This module verifies the formal bound numerically across realistic
parameter ranges and runs a mutation harness to confirm the test set
is not passing vacuously.

Run:
    python -m tools.sim.economics_risk_neutral_call

Or via pytest:
    pytest tools/sim/economics_risk_neutral_call.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def risk_neutral_call_nonneg_spec(S: float, K: float, T: float, r: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when max(S - K, 0) * exp(-r * T) >= 0, which the Lean
    theorem guarantees for any real S, K, r and T >= 0.
    """
    return max(S - K, 0) * math.exp(-r * T) >= 0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _drop_max(S: float, K: float, T: float, r: float) -> bool:
    """Drops the max: uses (S - K) instead of max(S - K, 0).
    Fails whenever S < K, producing a negative product."""
    return (S - K) * math.exp(-r * T) >= 0


def _negate(S: float, K: float, T: float, r: float) -> bool:
    """Negated price: -max(S - K, 0) * exp(-r * T) >= 0.
    Fails when S > K (negated positive intrinsic value times positive
    discount gives a strictly negative result).  Equals 0 when S <= K."""
    return -max(S - K, 0) * math.exp(-r * T) >= 0


def _strict_positive(S: float, K: float, T: float, r: float) -> bool:
    """Overconstrained: requires the price to exceed 0.01.
    Fails for out-of-the-money options (S <= K) where intrinsic value
    is zero, or for options far from expiry with small intrinsic value."""
    return max(S - K, 0) * math.exp(-r * T) > 0.01


# Realistic parameter ranges:
#   S, K on geometric scale: stock and strike from $1 to $1000,
#     covering deep ITM (S >> K) and deep OTM (S << K)
#   T on [0, 5]: same-day to five-year horizon; T=0 is the boundary case
#   r on [-0.05, 0.20]: slightly-negative (post-2008 reality) up to 20%
STRATEGY = Strategy(
    S=floats(1.0, 1000.0, log_scale=True),
    K=floats(1.0, 1000.0, log_scale=True),
    T=floats(0.0, 5.0),
    r=floats(-0.05, 0.20),
)

MUTATIONS = (
    Mutation(name="_drop_max", spec=_drop_max),
    Mutation(name="_negate", spec=_negate),
    Mutation(name="_strict_positive", spec=_strict_positive),
)


def main() -> int:
    result = run_harness(
        name="economics.risk_neutral_call_nonneg",
        spec=risk_neutral_call_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_risk_neutral_call_nonneg() -> None:
    result = run_harness(
        name="economics.risk_neutral_call_nonneg",
        spec=risk_neutral_call_nonneg_spec,
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
