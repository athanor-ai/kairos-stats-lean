"""Newton iteration positivity for `f(x) = x^2 - c`: empirical companion.

Lean side (`Pythia/Numerical/NewtonQuadraticIterPos.lean::newton_quadratic_iter_pos`)
proves: `(x + c / x) / 2 > 0` for all `c > 0` and `x > 0`. This is
the classical Babylonian / Heron square-root iteration: the
iterate `x_{n+1} = (x_n + c / x_n) / 2` for `f(x) = x^2 - c` stays
on the positive ray as long as it starts there.

This module verifies the formal positivity bound numerically across
many decades of `c` and `x` (log-scale to exercise both the
near-zero regime and the large-magnitude regime) and runs a mutation
harness to confirm the test set is not vacuous.

Run:
    python -m tools.sim.numerical_newton_quadratic_iter_pos

Or via pytest:
    pytest tools/sim/numerical_newton_quadratic_iter_pos.py
"""
from __future__ import annotations

from tools.sim.harness import Strategy, floats, run_harness
from tools.sim.mutations import (
    custom_transform,
    drop_factor,
    swap_inequality,
)


def newton_quadratic_iter_pos_spec(c: float, x: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when `(x + c / x) / 2 > 0`, which the Lean theorem
    guarantees for `c > 0` and `x > 0`. No float slack is needed for
    a strict positivity check on positive parameter draws.
    """
    return (x + c / x) / 2.0 > 0.0


# Mutations: standard library wrappers from tools.sim.mutations.


def _strict_lower_bound(c: float, x: float) -> bool:
    """Overconstrained claim: `(x + c / x) / 2 > 1e3`. Fails whenever
    both `c` and `x` are small (small AM-GM-like value)."""
    return (x + c / x) / 2.0 > 1.0e3


MUTATIONS = (
    swap_inequality(newton_quadratic_iter_pos_spec, name="swap_inequality"),
    # `drop_factor` pins x to -1.0; then (x + c / x) / 2 = (-1 - c) / 2,
    # which is strictly negative when c > 0 — i.e. on every draw.
    drop_factor(
        newton_quadratic_iter_pos_spec,
        "x",
        replacement=-1.0,
        name="drop_factor_x_negative",
        min_failure_rate=0.5,
    ),
    custom_transform(
        newton_quadratic_iter_pos_spec,
        _strict_lower_bound,
        name="strict_lower_bound_1e3",
        min_failure_rate=0.05,
    ),
)


# Wide log-scale ranges for c and x to exercise both the near-zero
# and the large-magnitude regimes of the iteration.
STRATEGY = Strategy(
    c=floats(1e-6, 1e6, log_scale=True),
    x=floats(1e-6, 1e6, log_scale=True),
)


def main() -> int:
    result = run_harness(
        name="numerical.newton_quadratic_iter_pos",
        spec=newton_quadratic_iter_pos_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_newton_quadratic_iter_pos() -> None:
    result = run_harness(
        name="numerical.newton_quadratic_iter_pos",
        spec=newton_quadratic_iter_pos_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=15,
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
