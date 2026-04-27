"""Hamming distance triangle inequality on 3-bit Boolean tuples: empirical companion.

Lean side (`Pythia/InfoTheory/HammingDistanceTriangle.lean::hamming_distance_triangle`)
proves: `d(a, c) <= d(a, b) + d(b, c)` for all 3-bit Boolean tuples
`a, b, c`, where `d` is the position-wise Hamming distance.

This module verifies the metric-axiom triangle inequality by
exhaustively sampling the 8x8x8 = 512 Boolean configurations (every
sweep grid point exercises a distinct configuration) and runs a
mutation harness so that incorrect distance definitions are
detectable on the same sample set.

Run:
    python -m tools.sim.infotheory_hamming_distance_triangle

Or via pytest:
    pytest tools/sim/infotheory_hamming_distance_triangle.py
"""
from __future__ import annotations

from tools.sim.harness import Strategy, choice, run_harness
from tools.sim.mutations import (
    custom_transform,
    swap_inequality,
)


def _hamming3(
    a0: bool, a1: bool, a2: bool,
    b0: bool, b1: bool, b2: bool,
) -> int:
    """Hamming distance between two 3-bit Boolean tuples: count of
    positions where the tuples differ."""
    return (
        (0 if a0 == b0 else 1)
        + (0 if a1 == b1 else 1)
        + (0 if a2 == b2 else 1)
    )


def hamming_distance_triangle_spec(
    a0: bool, a1: bool, a2: bool,
    b0: bool, b1: bool, b2: bool,
    c0: bool, c1: bool, c2: bool,
) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when `d(a, c) <= d(a, b) + d(b, c)`, which the Lean
    theorem guarantees for every assignment to the nine Booleans.
    """
    d_ac = _hamming3(a0, a1, a2, c0, c1, c2)
    d_ab = _hamming3(a0, a1, a2, b0, b1, b2)
    d_bc = _hamming3(b0, b1, b2, c0, c1, c2)
    return d_ac <= d_ab + d_bc


# Mutations: standard library wrappers from tools.sim.mutations.


def _drop_second_term(
    a0: bool, a1: bool, a2: bool,
    b0: bool, b1: bool, b2: bool,
    c0: bool, c1: bool, c2: bool,
) -> bool:
    """Mutated spec that drops `d(b, c)` from the RHS, asserting
    `d(a, c) <= d(a, b)`. Fails on every triple where `b` is closer
    to `a` than `c` is to `a`."""
    d_ac = _hamming3(a0, a1, a2, c0, c1, c2)
    d_ab = _hamming3(a0, a1, a2, b0, b1, b2)
    return d_ac <= d_ab


def _swap_d_ac_for_min(
    a0: bool, a1: bool, a2: bool,
    b0: bool, b1: bool, b2: bool,
    c0: bool, c1: bool, c2: bool,
) -> bool:
    """Mutated spec asserting strict triangle inequality `d(a,c) < d(a,b) + d(b,c)`,
    which fails on equality cases (e.g. when `b = a` so the bound is tight)."""
    d_ac = _hamming3(a0, a1, a2, c0, c1, c2)
    d_ab = _hamming3(a0, a1, a2, b0, b1, b2)
    d_bc = _hamming3(b0, b1, b2, c0, c1, c2)
    return d_ac < d_ab + d_bc


MUTATIONS = (
    swap_inequality(hamming_distance_triangle_spec, name="swap_inequality"),
    custom_transform(
        hamming_distance_triangle_spec,
        _drop_second_term,
        name="drop_second_term_d_bc",
        min_failure_rate=0.05,
    ),
    custom_transform(
        hamming_distance_triangle_spec,
        _swap_d_ac_for_min,
        name="strict_triangle_inequality",
        min_failure_rate=0.05,
    ),
)


# Exhaustive Boolean draws on each of the 9 components.
STRATEGY = Strategy(
    a0=choice(False, True),
    a1=choice(False, True),
    a2=choice(False, True),
    b0=choice(False, True),
    b1=choice(False, True),
    b2=choice(False, True),
    c0=choice(False, True),
    c1=choice(False, True),
    c2=choice(False, True),
)


def main() -> int:
    result = run_harness(
        name="info_theory.hamming_distance_triangle",
        spec=hamming_distance_triangle_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=2,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_hamming_distance_triangle() -> None:
    result = run_harness(
        name="info_theory.hamming_distance_triangle",
        spec=hamming_distance_triangle_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=2,
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
