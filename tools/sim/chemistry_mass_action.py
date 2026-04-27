"""Mass-action conservation for a single reversible reaction: empirical companion.

Lean side (`Pythia/Chemistry/MassActionConservation.lean::mass_action_conservation_pair`)
proves: for a reversible reaction A <=> B, given nA1 = nA0 - xi and
nB1 = nB0 + xi, we have nA0 + nB0 = nA1 + nB1.

This module verifies the conservation identity numerically across realistic
mole and reaction-extent ranges, then runs a mutation harness to confirm the
test set is not passing vacuously.

Run:
    python -m tools.sim.chemistry_mass_action

Or via pytest:
    pytest tools/sim/chemistry_mass_action.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    isclose,
    run_harness,
)


def mass_action_conservation_spec(nA0: float, nB0: float, xi: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True iff nA0 + nB0 == nA1 + nB1 (to within floating-point
    tolerance), where nA1 = nA0 - xi and nB1 = nB0 + xi.
    """
    nA1 = nA0 - xi
    nB1 = nB0 + xi
    return isclose(nA0 + nB0, nA1 + nB1, rtol=1e-9)


# Mutations: each one perturbs the spec so the claim should fail on
# a meaningful fraction of draws. The harness asserts every mutation
# fails on at least min_failure_rate of random inputs.

def _double_extent_one_side(nA0: float, nB0: float, xi: float) -> bool:
    """Extent applied twice to the A side but only once to the B side.

    nA1 = nA0 - 2*xi, nB1 = nB0 + xi. Conservation fails whenever xi != 0.
    """
    nA1 = nA0 - 2.0 * xi
    nB1 = nB0 + xi
    return isclose(nA0 + nB0, nA1 + nB1, rtol=1e-9)


def _negate_lhs(nA0: float, nB0: float, xi: float) -> bool:
    """Assert that the negated LHS equals the RHS.

    Checks -(nA0 + nB0) == nA1 + nB1. Fails whenever the total is nonzero.
    """
    nA1 = nA0 - xi
    nB1 = nB0 + xi
    return isclose(-(nA0 + nB0), nA1 + nB1, rtol=1e-9)


def _off_by_initial(nA0: float, nB0: float, xi: float) -> bool:
    """Assert conservation with a spurious +1.0 offset on the RHS.

    Checks nA0 + nB0 == nA1 + nB1 + 1.0. Fails always (off by 1.0).
    """
    nA1 = nA0 - xi
    nB1 = nB0 + xi
    return isclose(nA0 + nB0, nA1 + nB1 + 1.0, rtol=1e-9)


# Realistic parameter ranges:
#   nA0, nB0 : mole amounts of species A and B, 0 to 100 mol
#   xi       : reaction extent in mol, allowing negative (reverse reaction)
STRATEGY = Strategy(
    nA0=floats(0.0, 100.0),
    nB0=floats(0.0, 100.0),
    xi=floats(-50.0, 50.0),
)

MUTATIONS = (
    Mutation(name="double_extent_one_side", spec=_double_extent_one_side),
    Mutation(name="negate_lhs", spec=_negate_lhs),
    Mutation(name="off_by_initial", spec=_off_by_initial),
)


def main() -> int:
    result = run_harness(
        name="chemistry.mass_action_conservation_pair",
        spec=mass_action_conservation_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=8,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_mass_action_conservation_pair() -> None:
    result = run_harness(
        name="chemistry.mass_action_conservation_pair",
        spec=mass_action_conservation_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=8,
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
