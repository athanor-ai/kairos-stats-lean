"""Lotka-Volterra coexistence-equilibrium positivity -- empirical companion.

Lean side (`Pythia/Bio/Population.lean`) proves two theorems:

* `lotka_volterra_equilibrium_x_pos`: for gamma, delta > 0,
  x* = gamma / delta > 0.
* `lotka_volterra_equilibrium_y_pos`: for alpha, beta > 0,
  y* = alpha / beta > 0.

This module verifies both positivity results numerically across realistic
rate-parameter ranges and runs a mutation harness to confirm the test set
is not passing vacuously.

Run:
    python -m tools.sim.bio_lotka_volterra

Or via pytest:
    pytest tools/sim/bio_lotka_volterra.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def lotka_volterra_equilibrium_pos_spec(
    alpha: float, beta: float, gamma: float, delta: float
) -> bool:
    """The two positivity theorems evaluated numerically.

    Checks that x* = gamma/delta > 0 AND y* = alpha/beta > 0
    for strictly-positive rate parameters.
    """
    x_star = gamma / delta
    y_star = alpha / beta
    return x_star > 0 and y_star > 0


# ─── Mutations ────────────────────────────────────────────────────────
# Each deliberately breaks the spec. The harness asserts every mutation
# FAILS on >= 5 % of random draws, confirming the tests are not vacuous.

def _negate_x(
    alpha: float, beta: float, gamma: float, delta: float
) -> bool:
    """Wrong sign on x*: checks -gamma/delta > 0 instead of gamma/delta > 0."""
    x_star = -gamma / delta
    y_star = alpha / beta
    return x_star > 0 and y_star > 0


def _zero_alpha(
    alpha: float, beta: float, gamma: float, delta: float
) -> bool:
    """Zeroed alpha: checks gamma/delta > 0 and 0.0/beta > 0 (always False)."""
    x_star = gamma / delta
    y_star = 0.0 / beta
    return x_star > 0 and y_star > 0


def _swap_signs(
    alpha: float, beta: float, gamma: float, delta: float
) -> bool:
    """Negated both equilibria: checks -gamma/delta > 0 and -alpha/beta > 0."""
    x_star = -gamma / delta
    y_star = -alpha / beta
    return x_star > 0 and y_star > 0


STRATEGY = Strategy(
    alpha=floats(1e-3, 100, log_scale=True),
    beta=floats(1e-3, 100, log_scale=True),
    gamma=floats(1e-3, 100, log_scale=True),
    delta=floats(1e-3, 100, log_scale=True),
)

MUTATIONS = (
    Mutation(name="negate_x", spec=_negate_x),
    Mutation(name="zero_alpha", spec=_zero_alpha),
    Mutation(name="swap_signs", spec=_swap_signs),
)


def main() -> int:
    result = run_harness(
        name="bio.lotka_volterra_equilibrium_pos",
        spec=lotka_volterra_equilibrium_pos_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=4,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_lotka_volterra_equilibrium_pos() -> None:
    result = run_harness(
        name="bio.lotka_volterra_equilibrium_pos",
        spec=lotka_volterra_equilibrium_pos_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=4,
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
