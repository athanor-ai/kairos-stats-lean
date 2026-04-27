"""RC time constant positivity: empirical companion.

Lean side (`Pythia/Engineering/RCTimeConstant.lean::rc_time_constant_pos`)
proves: `R * C > 0` for all `R > 0` and `C > 0`.

This module verifies the formal bound numerically across realistic
parameter ranges (1 ohm to 10 M-ohm resistors, 1 pF to 1 mF capacitors)
and runs a mutation harness to confirm the test set is not vacuous.

Run:
    python -m tools.sim.engineering_rc_time_constant

Or via pytest:
    pytest tools/sim/engineering_rc_time_constant.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def rc_time_constant_pos_spec(R: float, C: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when R * C > 0, which the Lean theorem guarantees
    for all R > 0 and C > 0.
    """
    return R * C > 0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate_R(R: float, C: float) -> bool:
    """Negated R: (-R) * C > 0. Always False when R > 0 and C > 0."""
    return -R * C > 0


def _zero_C(R: float, C: float) -> bool:
    """Zero capacitance: R * 0.0 > 0. Always False."""
    return R * 0.0 > 0


def _strict_lower_bound(R: float, C: float) -> bool:
    """Overconstrained claim: R * C > 1e6.
    Fails whenever the product is small (e.g. small R or small C)."""
    return R * C > 1e6


# Realistic parameter ranges covering engineering use cases:
#   R: 1 ohm to 10 M-ohm (standard resistor range)
#   C: 1 pF to 1 mF (ceramic caps through electrolytic)
STRATEGY = Strategy(
    R=floats(1.0, 1e7, log_scale=True),
    C=floats(1e-12, 1e-3, log_scale=True),
)

MUTATIONS = (
    Mutation(name="negate_R", spec=_negate_R),
    Mutation(name="zero_C", spec=_zero_C),
    Mutation(name="strict_lower_bound", spec=_strict_lower_bound),
)


def main() -> int:
    result = run_harness(
        name="engineering.rc_time_constant_pos",
        spec=rc_time_constant_pos_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_rc_time_constant_pos() -> None:
    result = run_harness(
        name="engineering.rc_time_constant_pos",
        spec=rc_time_constant_pos_spec,
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
