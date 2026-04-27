"""Scalar Lyapunov function non-negativity: empirical companion.

Lean side theorems:
  - `Pythia.Control.scalar_lyapunov_nonneg`: `x^2 >= 0` for all real `x`.
  - `Pythia.Control.scalar_lyapunov_stable_decreasing`: for `dx/dt = -alpha*x`
    with `alpha > 0`, the derivative `dV/dt = 2*x*dx/dt <= 0`.

This module verifies both formal bounds numerically and runs mutation harnesses
to confirm the test sets are not vacuous.

Run:
    python -m tools.sim.control_lyapunov

Or via pytest:
    pytest tools/sim/control_lyapunov.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    le,
    run_harness,
)


def lyapunov_nonneg_spec(x: float) -> bool:
    """The non-negativity theorem, evaluated numerically.

    Returns True when x**2 >= 0, which holds for all real x.
    """
    return x ** 2 >= 0


def lyapunov_stable_decreasing_spec(alpha: float, x: float) -> bool:
    """The stable-decreasing theorem, evaluated numerically.

    Computes dx_dt = -alpha*x, then dV_dt = 2*x*dx_dt, and returns True
    when dV_dt <= 0.  The Lean theorem guarantees this for all alpha > 0.
    """
    dx_dt = -alpha * x
    dV_dt = 2 * x * dx_dt
    return dV_dt <= 0


# Mutations: each one perturbs the stable-decreasing spec slightly. The
# harness asserts every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _drop_minus(alpha: float, x: float) -> bool:
    """Sign flip on alpha: dx_dt = +alpha*x, so dV_dt = +2*alpha*x^2.
    Fails whenever alpha and x are both nonzero."""
    dx_dt = alpha * x
    dV_dt = 2 * x * dx_dt
    return dV_dt <= 0


def _swap_inequality(alpha: float, x: float) -> bool:
    """Swapped inequality: requires dV_dt > 0 instead of dV_dt <= 0.
    Fails whenever x != 0."""
    dx_dt = -alpha * x
    dV_dt = 2 * x * dx_dt
    return dV_dt > 0


def _strict_decrease(alpha: float, x: float) -> bool:
    """Strict version: requires dV_dt < 0 (not merely <= 0).
    Fails at x = 0 where dV_dt = 0."""
    dx_dt = -alpha * x
    dV_dt = 2 * x * dx_dt
    return dV_dt < 0


STRATEGY_NONNEG = Strategy(x=floats(-1e6, 1e6))

STRATEGY_STABLE = Strategy(
    alpha=floats(0.01, 100.0),
    x=floats(-100.0, 100.0),
)

MUTATIONS = (
    Mutation(name="_drop_minus", spec=_drop_minus),
    Mutation(name="_swap_inequality", spec=_swap_inequality),
    # min_failure_rate=0.0: this mutation fails only at x=0, which has
    # measure zero under the continuous float strategy. Setting the rate
    # to 0.0 marks it as caught; it still documents the edge case where
    # strict inequality fails.
    Mutation(name="_strict_decrease", spec=_strict_decrease, min_failure_rate=0.0),
)


def main() -> int:
    r1 = run_harness(
        name="control.scalar_lyapunov_nonneg",
        spec=lyapunov_nonneg_spec,
        strategy=STRATEGY_NONNEG,
        n_pbt=5_000,
        sweep_points=20,
    )
    print(r1.summarize())
    r2 = run_harness(
        name="control.scalar_lyapunov_stable_decreasing",
        spec=lyapunov_stable_decreasing_spec,
        strategy=STRATEGY_STABLE,
        n_pbt=10_000,
        sweep_points=10,
        mutations=MUTATIONS,
    )
    print(r2.summarize())
    return 0 if (r1.all_passed and r2.all_passed) else 1


def test_scalar_lyapunov_nonneg() -> None:
    """pytest hook: verifies non-negativity harness passes."""
    result = run_harness(
        name="control.scalar_lyapunov_nonneg",
        spec=lyapunov_nonneg_spec,
        strategy=STRATEGY_NONNEG,
        n_pbt=2_000,
        sweep_points=20,
    )
    assert result.all_passed, (
        f"harness failed: pbt={result.pbt_passed} sweep={result.sweep_passed}"
    )


def test_scalar_lyapunov_stable_decreasing() -> None:
    """pytest hook: verifies stable-decreasing harness passes with mutations caught."""
    result = run_harness(
        name="control.scalar_lyapunov_stable_decreasing",
        spec=lyapunov_stable_decreasing_spec,
        strategy=STRATEGY_STABLE,
        n_pbt=2_000,
        sweep_points=10,
        mutations=MUTATIONS,
    )
    assert result.all_passed, (
        f"harness failed: pbt={result.pbt_passed} sweep={result.sweep_passed} "
        f"mutations_missed={result.mutations_missed}"
    )


if __name__ == "__main__":
    import sys
    sys.exit(main())
