"""CRRA marginal utility positivity: empirical companion.

Lean side (`Pythia/Economics/CRRA.lean::crra_marginal_utility_pos`)
proves: `c^(-γ) > 0` for all `c > 0` and any `γ ∈ ℝ`.

This module verifies the formal bound numerically across realistic
parameter ranges and runs a mutation harness to confirm the test set
isn't passing vacuously.

Run:
    python -m tools.sim.economics_crra

Or via pytest:
    pytest tools/sim/economics_crra.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    isclose,
    run_harness,
)


def crra_mu_pos_spec(gamma: float, c: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when c**(-gamma) > 0, which the Lean theorem guarantees
    for all c > 0 and any real gamma.
    """
    return c ** (-gamma) > 0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate_output(gamma: float, c: float) -> bool:
    """Negated output: -(c**(-gamma)) > 0. Always False for c > 0."""
    return -(c ** (-gamma)) > 0


def _zero_consumption(gamma: float, c: float) -> bool:
    """Zero consumption: 0**(-gamma) > 0. Division by zero for gamma > 0;
    returns 0 > 0 for gamma < 0; both are False. Guard with try/except."""
    try:
        return 0.0 ** (-gamma) > 0
    except (ZeroDivisionError, OverflowError):
        return False


def _strict_positive_lower_bound(gamma: float, c: float) -> bool:
    """Overconstrained claim: c**(-gamma) > 1e9.
    Fails whenever c is large and gamma is positive, or c is small and
    gamma is sufficiently negative."""
    return c ** (-gamma) > 1e9


# Realistic parameter ranges covering three economic regimes:
#   gamma < 0: risk-loving (marginal utility rises with wealth)
#   gamma = 0: risk-neutral (linear utility, marginal utility = 1)
#   gamma > 0: risk-averse (the standard CRRA assumption)
#   c on geometric scale: household consumption from near-zero to
#   six orders of magnitude (covers micro to macro calibrations)
STRATEGY = Strategy(
    gamma=floats(-2.0, 5.0),
    c=floats(1e-3, 1e6, log_scale=True),
)

MUTATIONS = (
    Mutation(name="negate_output", spec=_negate_output),
    Mutation(name="zero_consumption", spec=_zero_consumption),
    Mutation(name="strict_positive_lower_bound", spec=_strict_positive_lower_bound),
)


def main() -> int:
    result = run_harness(
        name="economics.crra_marginal_utility_pos",
        spec=crra_mu_pos_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=10,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_crra_marginal_utility_pos() -> None:
    result = run_harness(
        name="economics.crra_marginal_utility_pos",
        spec=crra_mu_pos_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=10,
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
