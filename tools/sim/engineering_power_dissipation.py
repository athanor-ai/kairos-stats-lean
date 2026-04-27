"""Ohm's law power dissipation non-negativity: empirical companion.

Lean side (`Pythia/Engineering/PowerDissipation.lean::power_dissipation_nonneg`)
proves: `I^2 * R >= 0` for all `I : real` and `R >= 0`.

This module verifies the formal bound numerically across realistic
parameter ranges (currents +/- 100 A, resistances 1 ohm to 1 M-ohm)
and runs a mutation harness to confirm the test set is not vacuous.

Run:
    python -m tools.sim.engineering_power_dissipation

Or via pytest:
    pytest tools/sim/engineering_power_dissipation.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def power_dissipation_nonneg_spec(I: float, R: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when I**2 * R >= 0, which the Lean theorem guarantees
    for all I (any real) and R >= 0.
    """
    return I**2 * R >= 0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate(I: float, R: float) -> bool:
    """Negated result: -(I**2 * R) >= 0.
    Fails when I and R are both nonzero (result is strictly negative)."""
    return -(I**2 * R) >= 0


def _drop_square(I: float, R: float) -> bool:
    """Drop the square: I * R >= 0.
    Fails when I < 0 and R > 0 (product is negative)."""
    return I * R >= 0


def _strict_positive(I: float, R: float) -> bool:
    """Overconstrained claim: I**2 * R > 1e8.
    Fails when I or R is small (product is at most 1e8)."""
    return I**2 * R > 1e8


# Realistic parameter ranges covering engineering use cases:
#   I: -100 A to +100 A (standard current range)
#   R: 1e-3 ohm to 1 M-ohm (log-scale; lower bound > 0 required for log_scale)
STRATEGY = Strategy(
    I=floats(-100.0, 100.0),
    R=floats(1e-3, 1e6, log_scale=True),
)

MUTATIONS = (
    Mutation(name="negate", spec=_negate),
    Mutation(name="drop_square", spec=_drop_square),
    Mutation(name="strict_positive", spec=_strict_positive),
)


def main() -> int:
    result = run_harness(
        name="engineering.power_dissipation_nonneg",
        spec=power_dissipation_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_power_dissipation_nonneg() -> None:
    result = run_harness(
        name="engineering.power_dissipation_nonneg",
        spec=power_dissipation_nonneg_spec,
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
