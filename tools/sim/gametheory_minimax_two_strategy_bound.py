"""Weak minimax inequality (2x2 case): empirical companion.

Lean side (`Pythia/GameTheory/MinimaxTwoStrategyBound.lean::minimax_two_strategy_bound`)
proves: `max_i min_j A i j <= min_j max_i A i j` for any 2x2 real
payoff matrix `A : Fin 2 -> Fin 2 -> R`.

This module verifies the formal bound numerically across uniformly-
drawn 2x2 matrices and runs a mutation harness to confirm the test
set is not vacuous.

Run:
    python -m tools.sim.gametheory_minimax_two_strategy_bound

Or via pytest:
    pytest tools/sim/gametheory_minimax_two_strategy_bound.py
"""
from __future__ import annotations

from tools.sim.harness import Strategy, floats, run_harness
from tools.sim.mutations import (
    custom_transform,
    swap_inequality,
)


def _maxmin(a00: float, a01: float, a10: float, a11: float) -> float:
    """max_i min_j A i j  for the 2x2 matrix [[a00,a01],[a10,a11]]."""
    return max(min(a00, a01), min(a10, a11))


def _minmax(a00: float, a01: float, a10: float, a11: float) -> float:
    """min_j max_i A i j  for the 2x2 matrix [[a00,a01],[a10,a11]]."""
    return min(max(a00, a10), max(a01, a11))


def minimax_two_strategy_bound_spec(
    a00: float, a01: float, a10: float, a11: float
) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when `max_i min_j A i j <= min_j max_i A i j`,
    which the Lean theorem guarantees for any 2x2 real payoff matrix.
    Tiny float slack is included so equality cases (saddle points)
    pass cleanly under rounding.
    """
    lhs = _maxmin(a00, a01, a10, a11)
    rhs = _minmax(a00, a01, a10, a11)
    return lhs <= rhs + 1e-12


# Mutations: standard library wrappers from tools.sim.mutations plus a
# strict-bound custom_transform.


def _swap_max_min_outer(a00: float, a01: float, a10: float, a11: float) -> bool:
    """Swap outer operators: claim `min_i max_j A i j <= max_j min_i A i j`.
    This is the OPPOSITE direction; it fails on roughly half the
    matrices (the strong-minimax direction is only true with mixed
    strategies)."""
    # min_i max_j A i j  =  min(max(a00, a01), max(a10, a11))
    lhs = min(max(a00, a01), max(a10, a11))
    # max_j min_i A i j  =  max(min(a00, a10), min(a01, a11))
    rhs = max(min(a00, a10), min(a01, a11))
    return lhs <= rhs - 1e-9


def _strict_zero_gap(a00: float, a01: float, a10: float, a11: float) -> bool:
    """Overconstrained claim: gap is strictly zero, i.e.
    `max_i min_j A i j == min_j max_i A i j`. Fails on most matrices
    (only saddle-point matrices have zero gap)."""
    lhs = _maxmin(a00, a01, a10, a11)
    rhs = _minmax(a00, a01, a10, a11)
    return abs(rhs - lhs) < 1e-9


MUTATIONS = (
    swap_inequality(
        minimax_two_strategy_bound_spec,
        name="swap_inequality",
        # Negation: max_i min_j A > min_j max_i A. Holds only for the
        # measure-zero saddle locus, so the negated spec is False on
        # essentially every random matrix. Floor at 0.5 conservatively.
        min_failure_rate=0.5,
    ),
    custom_transform(
        minimax_two_strategy_bound_spec,
        _swap_max_min_outer,
        name="swap_max_min_outer",
        min_failure_rate=0.3,
    ),
    custom_transform(
        minimax_two_strategy_bound_spec,
        _strict_zero_gap,
        name="strict_zero_gap",
        min_failure_rate=0.3,
    ),
)


# Parameter ranges:
#   a00..a11: each entry uniform in [-10, 10]
STRATEGY = Strategy(
    a00=floats(-10.0, 10.0),
    a01=floats(-10.0, 10.0),
    a10=floats(-10.0, 10.0),
    a11=floats(-10.0, 10.0),
)


def main() -> int:
    result = run_harness(
        name="gametheory.minimax_two_strategy_bound",
        spec=minimax_two_strategy_bound_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_minimax_two_strategy_bound() -> None:
    result = run_harness(
        name="gametheory.minimax_two_strategy_bound",
        spec=minimax_two_strategy_bound_spec,
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
        f"vacuous-test risk: {result.mutations_missed}"
    )


if __name__ == "__main__":
    import sys
    sys.exit(main())
