"""Carnot heat-engine efficiency upper bound: empirical companion.

Lean side (`Pythia/Thermodynamics/CarnotEfficiencyUpperBound.lean::carnot_efficiency_upper_bound`)
proves: `1 - T_c / T_h <= 1` for all reservoir temperatures
`0 < T_c < T_h` (Carnot, 1824).

This module verifies the formal bound numerically across realistic
absolute-temperature ranges (Kelvin scale, sub-cryogenic to stellar)
and runs a mutation harness to confirm the test set is not passing
vacuously.

Run:
    python -m tools.sim.thermodynamics_carnot_efficiency_upper_bound

Or via pytest:
    pytest tools/sim/thermodynamics_carnot_efficiency_upper_bound.py
"""
from __future__ import annotations

from tools.sim.harness import Strategy, floats, run_harness
from tools.sim.mutations import (
    custom_transform,
    negate_value,
    swap_inequality,
)


def carnot_efficiency_upper_bound_spec(T_c: float, T_h_offset: float) -> bool:
    """The theorem itself, evaluated numerically.

    Parametrized by the cold-reservoir temperature `T_c` and a strictly
    positive offset `T_h_offset` so `T_h = T_c + T_h_offset > T_c > 0`,
    matching the Lean hypotheses `0 < T_c` and `T_c < T_h`.

    Returns True when the Carnot efficiency `1 - T_c / T_h` is bounded
    above by 1, with a tiny float slack for boundary rounding.
    """
    T_h = T_c + T_h_offset
    eta = 1.0 - T_c / T_h
    return eta <= 1.0 + 1e-12


# Mutations: standard library wrappers from tools.sim.mutations.

def _drop_T_c_subtraction(T_c: float, T_h_offset: float) -> bool:
    """Mutated spec that drops the leading `1 -` and demands the bare
    ratio `T_c / T_h` be at most 1 minus a fixed slack of 0.5. This
    fails on every draw where the ratio exceeds 0.5, which is most
    of the parameter cube under the chosen strategy."""
    T_h = T_c + T_h_offset
    return (T_c / T_h) <= 0.5 + 1e-12


MUTATIONS = (
    swap_inequality(carnot_efficiency_upper_bound_spec, name="swap_inequality"),
    negate_value(carnot_efficiency_upper_bound_spec, name="negate_value"),
    custom_transform(
        carnot_efficiency_upper_bound_spec,
        _drop_T_c_subtraction,
        name="drop_one_minus_factor",
        min_failure_rate=0.05,
    ),
)


# Realistic Kelvin-scale temperature ranges. T_c covers cryogenic
# (10 mK) through near-stellar (1 000 K); the offset spans the same
# decades so the ratio T_c / T_h sweeps the open unit interval.
STRATEGY = Strategy(
    T_c=floats(0.01, 1000.0),
    T_h_offset=floats(0.01, 1000.0),
)


def main() -> int:
    result = run_harness(
        name="thermodynamics.carnot_efficiency_upper_bound",
        spec=carnot_efficiency_upper_bound_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=15,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_carnot_efficiency_upper_bound() -> None:
    result = run_harness(
        name="thermodynamics.carnot_efficiency_upper_bound",
        spec=carnot_efficiency_upper_bound_spec,
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
