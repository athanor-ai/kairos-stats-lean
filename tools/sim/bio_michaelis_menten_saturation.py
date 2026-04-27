"""Michaelis-Menten saturation: empirical companion.

Lean side (`Pythia/Bio/MichaelisMentenSaturation.lean::michaelis_menten_saturation`)
proves: `Vmax * S / (Km + S) <= Vmax` for all `Vmax >= 0`, `Km > 0`,
`S >= 0` (Michaelis & Menten, 1913).

This module verifies the formal saturation bound numerically across
biologically realistic substrate concentrations and Km values
(spanning many orders of magnitude) and runs a mutation harness to
confirm the test set is not passing vacuously.

Run:
    python -m tools.sim.bio_michaelis_menten_saturation

Or via pytest:
    pytest tools/sim/bio_michaelis_menten_saturation.py
"""
from __future__ import annotations

from tools.sim.harness import Strategy, floats, run_harness
from tools.sim.mutations import (
    custom_transform,
    drop_factor,
    swap_inequality,
)


def michaelis_menten_saturation_spec(Vmax: float, Km: float, S: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when `Vmax * S / (Km + S) <= Vmax`, which the Lean
    theorem guarantees for all `Vmax >= 0`, `Km > 0`, `S >= 0`. A
    tiny float slack accounts for rounding when `S >> Km` (the
    saturation regime where the LHS approaches Vmax).
    """
    v = Vmax * S / (Km + S)
    return v <= Vmax + 1e-9 * max(1.0, abs(Vmax))


# Mutations: standard library wrappers from tools.sim.mutations.


def _swap_numerator_denominator(Vmax: float, Km: float, S: float) -> bool:
    """Mutated spec with numerator and denominator interchanged:
    `Vmax * (Km + S) / S <= Vmax`. For Km > 0 the LHS strictly exceeds
    Vmax whenever both Vmax and S are positive."""
    if S <= 0:
        # Avoid division-by-zero on the boundary; harness still
        # detects the mutation on positive-S draws.
        return True
    lhs = Vmax * (Km + S) / S
    return lhs <= Vmax + 1e-9 * max(1.0, abs(Vmax))


MUTATIONS = (
    swap_inequality(michaelis_menten_saturation_spec, name="swap_inequality"),
    # `drop_factor` overrides Vmax with -1.0; the bound 'v <= -1.0'
    # then fails on every draw where the original Vmax * S / (Km + S)
    # is non-negative, i.e. essentially all of them.
    drop_factor(
        michaelis_menten_saturation_spec,
        "Vmax",
        replacement=-1.0,
        name="drop_factor_vmax_negative",
        min_failure_rate=0.05,
    ),
    custom_transform(
        michaelis_menten_saturation_spec,
        _swap_numerator_denominator,
        name="swap_numerator_denominator",
        min_failure_rate=0.05,
    ),
)


# Biologically realistic ranges:
#   Vmax: 0 to ~1e3 (turnover-rate units; bound generously)
#   Km  : 1e-3 to 1e3 mol/L on a log scale (substrate-affinity range)
#   S   : 0 to 1e6 (large excess to exercise the saturation regime)
STRATEGY = Strategy(
    Vmax=floats(0.0, 1e3),
    Km=floats(1e-3, 1e3, log_scale=True),
    S=floats(0.0, 1e6),
)


def main() -> int:
    result = run_harness(
        name="bio.michaelis_menten_saturation",
        spec=michaelis_menten_saturation_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=10,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_michaelis_menten_saturation() -> None:
    result = run_harness(
        name="bio.michaelis_menten_saturation",
        spec=michaelis_menten_saturation_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=10,
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
