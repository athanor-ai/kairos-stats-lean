"""Arrhenius rate constant positivity: empirical companion.

Lean side (`Pythia/Chemistry/Arrhenius.lean::arrhenius_pos`)
proves: `A * exp(-Eₐ / (R * T)) > 0` for all `A > 0`, `R > 0`, `T > 0`
and any `Eₐ ∈ ℝ`.

This module verifies the formal bound numerically across realistic
parameter ranges, then runs a mutation harness to confirm the test
set is not passing vacuously.

Run:
    python -m tools.sim.chemistry_arrhenius

Or via pytest:
    pytest tools/sim/chemistry_arrhenius.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    isclose,
    run_harness,
)


def arrhenius_pos_spec(A: float, Ea: float, R: float, T: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True iff A * exp(-Ea / (R * T)) > 0.
    """
    return A * math.exp(-Ea / (R * T)) > 0


# Mutations: each one perturbs the spec so the claim should fail on
# a meaningful fraction of draws. The harness asserts every mutation
# fails on at least min_failure_rate of random inputs.

def _negated_A(A: float, Ea: float, R: float, T: float) -> bool:
    """Negate the pre-exponential factor. Result is negative when A > 0,
    so strictly-positive claim fails."""
    return -A * math.exp(-Ea / (R * T)) > 0


def _zero_A(A: float, Ea: float, R: float, T: float) -> bool:
    """Zero out the pre-exponential factor. Result is 0, not strictly
    positive, so the claim fails."""
    return 0.0 * math.exp(-Ea / (R * T)) > 0


def _much_stronger_bound(A: float, Ea: float, R: float, T: float) -> bool:
    """Assert rate > 1e9 instead of rate > 0. Fails whenever A is small
    or the exponential suppression is large."""
    return A * math.exp(-Ea / (R * T)) > 1e9


# Realistic parameter ranges:
#   A   : pre-exponential factor, geometric scale 1e-3 to 1e15 (covers
#         surface reactions to gas-phase collision rates)
#   Ea  : activation energy, 0 to 500 kJ/mol in J/mol units
#   R   : gas constant, narrowly around 8.314 J/(mol.K)
#   T   : absolute temperature, 200 K (cold) to 2000 K (flame)
STRATEGY = Strategy(
    A=floats(1e-3, 1e15, log_scale=True),
    Ea=floats(0, 5e5),
    R=floats(8.0, 9.0),
    T=floats(200.0, 2000.0),
)

MUTATIONS = (
    Mutation(name="negated_A", spec=_negated_A),
    Mutation(name="zero_A", spec=_zero_A),
    Mutation(name="much_stronger_bound_1e9", spec=_much_stronger_bound),
)


def main() -> int:
    result = run_harness(
        name="chemistry.arrhenius_pos",
        spec=arrhenius_pos_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_arrhenius_pos() -> None:
    result = run_harness(
        name="chemistry.arrhenius_pos",
        spec=arrhenius_pos_spec,
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
