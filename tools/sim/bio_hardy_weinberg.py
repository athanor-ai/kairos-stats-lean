"""Hardy-Weinberg allele-frequency conservation -- empirical companion.

Lean side (`Pythia/Bio/Population.lean::hardy_weinberg_conservation`)
proves: `p^2 + 2*p*q + q^2 = 1` for all `p, q` with `p + q = 1`.

This module verifies the formal identity numerically across realistic
allele-frequency ranges and runs a mutation harness to confirm the
test set is not passing vacuously.

Run:
    python -m tools.sim.bio_hardy_weinberg

Or via pytest:
    pytest tools/sim/bio_hardy_weinberg.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    isclose,
    run_harness,
)


def hardy_weinberg_spec(p: float) -> bool:
    """The theorem itself, evaluated numerically.

    Takes p in [0, 1], derives q = 1 - p, then checks:

        p^2 + 2*p*q + q^2 == 1.0

    Returns True when the equality holds within rtol=1e-9.
    """
    q = 1 - p
    return isclose(p ** 2 + 2 * p * q + q ** 2, 1.0, rtol=1e-9)


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of the random draws --
# if any mutation passes, the original test set is vacuous.

def _drop_cross_term(p: float) -> bool:
    """Forgot the coefficient 2 in the heterozygous term 2pq."""
    q = 1 - p
    return isclose(p ** 2 + p * q + q ** 2, 1.0, rtol=1e-9)


def _off_by_one_target(p: float) -> bool:
    """Wrong target: check that the sum equals 0.5 instead of 1.0."""
    q = 1 - p
    return isclose(p ** 2 + 2 * p * q + q ** 2, 0.5, rtol=1e-9)


def _wrong_q_formula(p: float) -> bool:
    """Wrong constraint: derive q = 1 + p instead of 1 - p."""
    q = 1 + p
    return isclose(p ** 2 + 2 * p * q + q ** 2, 1.0, rtol=1e-9)


STRATEGY = Strategy(p=floats(0.0, 1.0))

MUTATIONS = (
    Mutation(name="drop_cross_term", spec=_drop_cross_term),
    Mutation(name="off_by_one_target", spec=_off_by_one_target),
    Mutation(name="wrong_q_formula", spec=_wrong_q_formula),
)


def main() -> int:
    result = run_harness(
        name="bio.hardy_weinberg",
        spec=hardy_weinberg_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=20,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_hardy_weinberg() -> None:
    result = run_harness(
        name="bio.hardy_weinberg",
        spec=hardy_weinberg_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=20,
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
