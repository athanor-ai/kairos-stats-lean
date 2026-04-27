"""Hooke's law spring potential energy non-negativity: empirical companion.

Lean side (`Pythia/Mechanical/HookeSpring.lean::hooke_pe_nonneg`)
proves: `(1/2) * k * x^2 >= 0` for all `k >= 0` and any `x : real`.

This module verifies the formal bound numerically across realistic
parameter ranges (spring constants 0 N/m to 1 MN/m, displacements
-10 m to 10 m) and runs a mutation harness to confirm the test set
is not vacuous.

Run:
    python -m tools.sim.mechanical_hooke_spring

Or via pytest:
    pytest tools/sim/mechanical_hooke_spring.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def hooke_pe_nonneg_spec(k: float, x: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when 0.5 * k * x**2 >= 0, which the Lean theorem
    guarantees for all k >= 0 and any real displacement x.
    """
    return 0.5 * k * x**2 >= 0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate_pe(k: float, x: float) -> bool:
    """Negated PE: -(0.5 * k * x**2) >= 0.
    Fails when k > 0 and x != 0, since the product is then strictly negative."""
    return -(0.5 * k * x**2) >= 0


def _drop_square(k: float, x: float) -> bool:
    """Linearised displacement: 0.5 * k * x >= 0.
    Fails when k > 0 and x < 0, unlike the true quadratic."""
    return 0.5 * k * x >= 0


def _strict_positive(k: float, x: float) -> bool:
    """Overconstrained claim: 0.5 * k * x**2 > 1e13.
    Fails whenever k or x is not near the upper extreme of the range
    (e.g. spring constant below ~1e7 N/m or displacement below ~sqrt(2e13) m)."""
    return 0.5 * k * x**2 > 1e13


# Realistic parameter ranges covering engineering use cases:
#   k: 0 N/m to 1 MN/m (soft rubber band through stiff industrial spring)
#   x: -10 m to 10 m (engineering-scale displacements)
STRATEGY = Strategy(
    k=floats(0.0, 1e6),
    x=floats(-10.0, 10.0),
)

MUTATIONS = (
    Mutation(name="negate_pe", spec=_negate_pe),
    Mutation(name="drop_square", spec=_drop_square),
    Mutation(name="strict_positive", spec=_strict_positive),
)


def main() -> int:
    result = run_harness(
        name="mechanical.hooke_pe_nonneg",
        spec=hooke_pe_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_hooke_pe_nonneg() -> None:
    result = run_harness(
        name="mechanical.hooke_pe_nonneg",
        spec=hooke_pe_nonneg_spec,
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
