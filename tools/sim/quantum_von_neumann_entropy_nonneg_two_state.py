"""Two-state von Neumann entropy non-negativity: empirical companion.

Lean side (`Pythia/Quantum/VonNeumannEntropyNonnegTwoState.lean::von_neumann_entropy_nonneg_two_state`)
proves: `H(p) = -p log p - (1-p) log(1-p) >= 0` for any p in [0, 1],
the diagonal-basis qubit von Neumann entropy.

This module verifies the formal bound numerically across the unit
interval and runs a mutation harness to confirm the test set is
not vacuous.

Run:
    python -m tools.sim.quantum_von_neumann_entropy_nonneg_two_state

Or via pytest:
    pytest tools/sim/quantum_von_neumann_entropy_nonneg_two_state.py
"""
from __future__ import annotations

import math

from tools.sim.harness import Strategy, floats, run_harness
from tools.sim.mutations import (
    custom_transform,
    swap_inequality,
)


def _neg_mul_log(x: float) -> float:
    """Compute -x * log(x) with the convention 0 * log(0) = 0."""
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log(x)


def von_neumann_entropy_nonneg_two_state_spec(p: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when `H(p) = -p log p - (1-p) log(1-p) >= 0`, the
    diagonal-basis two-state von Neumann entropy. The Lean theorem
    guarantees this for all p in [0, 1]; tiny float slack at the
    boundary handles 0 * log 0 conventions.
    """
    H = _neg_mul_log(p) + _neg_mul_log(1 - p)
    return H >= -1e-12


# Mutations: standard library wrappers from tools.sim.mutations plus a
# strict-bound custom_transform.


def _strict_above_log2(p: float) -> bool:
    """Overconstrained claim: `H(p) >= log 2 = 0.693`, the maximum
    entropy at p=0.5. Fails at the boundaries (p near 0 or 1) where
    H drops to 0."""
    H = _neg_mul_log(p) + _neg_mul_log(1 - p)
    return H >= math.log(2)


def _drop_second_term(p: float) -> bool:
    """Drop the second term: `-p log p >= 0`. Holds for p in [0, 1]
    so the mutation passes everywhere; we instead subtract a constant
    of 0.5 to break it at the boundaries."""
    return _neg_mul_log(p) - 0.5 >= 0.0


MUTATIONS = (
    swap_inequality(
        von_neumann_entropy_nonneg_two_state_spec,
        name="swap_inequality",
        # Inequality is non-strict and equality holds at p=0 and p=1,
        # so the negated claim H(p) <= 0 holds at the boundaries.
        # On a uniform [0,1] draw the negation fails almost everywhere
        # (i.e. the negated spec is False), so swap is detectable on
        # ~99% of draws. Floor the rate at 0.5 conservatively.
        min_failure_rate=0.5,
    ),
    custom_transform(
        von_neumann_entropy_nonneg_two_state_spec,
        _strict_above_log2,
        name="strict_above_log2",
        min_failure_rate=0.05,
    ),
    custom_transform(
        von_neumann_entropy_nonneg_two_state_spec,
        _drop_second_term,
        name="drop_second_term_minus_half",
        min_failure_rate=0.05,
    ),
)


# Parameter range: full unit interval.
STRATEGY = Strategy(
    p=floats(0.0, 1.0),
)


def main() -> int:
    result = run_harness(
        name="quantum.von_neumann_entropy_nonneg_two_state",
        spec=von_neumann_entropy_nonneg_two_state_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=20,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_von_neumann_entropy_nonneg_two_state() -> None:
    result = run_harness(
        name="quantum.von_neumann_entropy_nonneg_two_state",
        spec=von_neumann_entropy_nonneg_two_state_spec,
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
        f"vacuous-test risk: {result.mutations_missed}"
    )


if __name__ == "__main__":
    import sys
    sys.exit(main())
