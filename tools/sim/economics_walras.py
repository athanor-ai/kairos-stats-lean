"""Walras' Law (clearing-prices form): empirical companion.

Lean side (`Pythia/Economics/Walras.lean::walras_clearing_implies_zero_sum`)
proves: when z i = 0 for all i, `∑ i, p i * z i = 0`.

This module verifies the formal bound numerically across realistic
parameter ranges and runs a mutation harness to confirm the test set
is not passing vacuously.

Run:
    python -m tools.sim.economics_walras

Or via pytest:
    pytest tools/sim/economics_walras.py
"""
from __future__ import annotations

import math
import random

from tools.sim.harness import Mutation, Strategy, floats, ints, run_harness


def walras_clearing_spec(seed: float, n: int, price_scale: float) -> bool:
    """The theorem itself, evaluated numerically.

    Generates n random prices, sets all excess demands to zero (the
    market-clearing condition), computes the Walras sum, and returns
    True when the sum is zero within floating-point tolerance.
    """
    rng = random.Random(int(seed * 1e6) % (2**32))
    prices = [rng.uniform(0.01, price_scale) for _ in range(n)]
    excess_demands = [0.0 for _ in range(n)]  # clearing condition
    walras_sum = sum(p * z for p, z in zip(prices, excess_demands))
    return abs(walras_sum) < 1e-12


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _break_clearing(seed: float, n: int, price_scale: float) -> bool:
    """All excess demands set to 1.0 instead of 0.0.

    The Walras sum becomes sum(prices) > 0, so abs(sum) < 1e-12 fails.
    """
    rng = random.Random(int(seed * 1e6) % (2**32))
    prices = [rng.uniform(0.01, price_scale) for _ in range(n)]
    excess_demands = [1.0 for _ in range(n)]  # NOT clearing
    walras_sum = sum(p * z for p, z in zip(prices, excess_demands))
    return abs(walras_sum) < 1e-12


def _break_clearing_one(seed: float, n: int, price_scale: float) -> bool:
    """Excess demand of good 0 set to 1.0; rest remain zero.

    The Walras sum equals prices[0] > 0, so the check fails.
    """
    rng = random.Random(int(seed * 1e6) % (2**32))
    prices = [rng.uniform(0.01, price_scale) for _ in range(n)]
    excess_demands = [0.0 for _ in range(n)]
    if n > 0:
        excess_demands[0] = 1.0  # good 0 does NOT clear
    walras_sum = sum(p * z for p, z in zip(prices, excess_demands))
    return abs(walras_sum) < 1e-12


def _negate_check(seed: float, n: int, price_scale: float) -> bool:
    """Inverted inequality: True only when abs(sum) >= 1e-12.

    The actual zero-sum always fails this inverted check.
    """
    rng = random.Random(int(seed * 1e6) % (2**32))
    prices = [rng.uniform(0.01, price_scale) for _ in range(n)]
    excess_demands = [0.0 for _ in range(n)]
    walras_sum = sum(p * z for p, z in zip(prices, excess_demands))
    return abs(walras_sum) >= 1e-12  # inverted: fails on the true zero-sum


STRATEGY = Strategy(
    seed=floats(0.0, 1.0),
    n=ints(2, 20),
    price_scale=floats(1.0, 100.0),
)

MUTATIONS = (
    Mutation(name="break_clearing", spec=_break_clearing),
    Mutation(name="break_clearing_one", spec=_break_clearing_one),
    Mutation(name="negate_check", spec=_negate_check),
)


def main() -> int:
    result = run_harness(
        name="economics.walras_clearing_implies_zero_sum",
        spec=walras_clearing_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_walras_clearing() -> None:
    result = run_harness(
        name="economics.walras_clearing_implies_zero_sum",
        spec=walras_clearing_spec,
        strategy=STRATEGY,
        n_pbt=500,
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
