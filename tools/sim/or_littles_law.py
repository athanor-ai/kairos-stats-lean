"""Little's Law non-negativity: empirical companion.

Lean side (`Pythia/OR/LittlesLaw.lean::littles_law_nonneg`)
proves: `lam * W >= 0` for all `lam >= 0` and `W >= 0`.

This module verifies the formal bound numerically across realistic
parameter ranges and runs a mutation harness to confirm the test set
isn't passing vacuously.

Run:
    python -m tools.sim.or_littles_law

Or via pytest:
    pytest tools/sim/or_littles_law.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def littles_law_nonneg_spec(lam: float, W: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when lam * W >= 0, which the Lean theorem guarantees
    for all lam >= 0 and W >= 0.
    """
    return lam * W >= 0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate_lambda(lam: float, W: float) -> bool:
    """Negated lambda: -lam * W >= 0. Fails when lam > 0 and W > 0."""
    return -lam * W >= 0


def _negate_W(lam: float, W: float) -> bool:
    """Negated W: lam * -W >= 0. Fails when lam > 0 and W > 0."""
    return lam * -W >= 0


def _strict_positive_lower(lam: float, W: float) -> bool:
    """Overconstrained claim: lam * W > 100.0.
    Fails whenever the product is small (e.g. near-zero arrival rate or
    near-zero sojourn time)."""
    return lam * W > 100.0


# Realistic parameter ranges for queueing systems:
#   lam: arrival rate in customers/sec, from near-zero to high throughput
#   W: mean sojourn time in seconds, from subsecond to extended waits
STRATEGY = Strategy(
    lam=floats(0.0, 1000.0),
    W=floats(0.0, 100.0),
)

MUTATIONS = (
    Mutation(name="_negate_lambda", spec=_negate_lambda),
    Mutation(name="_negate_W", spec=_negate_W),
    Mutation(name="_strict_positive_lower", spec=_strict_positive_lower,
             min_failure_rate=0.005),
)


def main() -> int:
    result = run_harness(
        name="or.littles_law_nonneg",
        spec=littles_law_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_littles_law_nonneg() -> None:
    result = run_harness(
        name="or.littles_law_nonneg",
        spec=littles_law_nonneg_spec,
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
