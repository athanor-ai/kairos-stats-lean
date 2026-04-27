"""CAPM beta nonnegativity: empirical companion.

Lean side (`Pythia/Economics/CAPM.lean::capm_beta_nonneg`)
proves: `cov / varM >= 0` for all `cov >= 0` and `varM > 0`.

This module verifies the formal bound numerically across realistic
parameter ranges and runs a mutation harness to confirm the test set
isn't passing vacuously.

Run:
    python -m tools.sim.economics_capm

Or via pytest:
    pytest tools/sim/economics_capm.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def capm_beta_nonneg_spec(cov: float, varM: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when cov / varM >= 0, which the Lean theorem guarantees
    for all cov >= 0 and varM > 0.
    """
    return cov / varM >= 0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate(cov: float, varM: float) -> bool:
    """Negated numerator: -cov / varM >= 0. Fails when cov > 0."""
    return -cov / varM >= 0


def _use_neg_var(cov: float, varM: float) -> bool:
    """Negated denominator: cov / -varM >= 0. Fails when cov > 0."""
    return cov / -varM >= 0


def _strict_positive(cov: float, varM: float) -> bool:
    """Overconstrained claim: cov / varM > 0.5. Fails when cov is small."""
    return cov / varM > 0.5


# Covariance drawn from [0, 1] (nonnegative per theorem hypothesis).
# Variance drawn log-uniformly from [1e-6, 10] (strictly positive).
STRATEGY = Strategy(
    cov=floats(0.0, 1.0),
    varM=floats(1e-6, 10.0, log_scale=True),
)

MUTATIONS = (
    Mutation(name="negate", spec=_negate),
    Mutation(name="use_neg_var", spec=_use_neg_var),
    Mutation(name="strict_positive", spec=_strict_positive),
)


def main() -> int:
    result = run_harness(
        name="economics.capm_beta_nonneg",
        spec=capm_beta_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_capm_beta_nonneg() -> None:
    result = run_harness(
        name="economics.capm_beta_nonneg",
        spec=capm_beta_nonneg_spec,
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
