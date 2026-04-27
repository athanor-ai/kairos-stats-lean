"""Discrete L1 Wasserstein-style cost non-negativity: empirical companion.

Lean side (`Pythia/OptimalTransport/WassersteinDistanceNonneg.lean::wasserstein_distance_nonneg`)
proves: `sum_i |p_i - q_i| >= 0` for any two real-valued maps
`p, q : Fin n -> R`.

This module verifies the formal bound numerically across realistic
parameter ranges (vector lengths 1 to 50, amplitudes 0.1 to 10) and
runs a mutation harness to confirm the test set is not vacuous.

Run:
    python -m tools.sim.optimaltransport_wasserstein_distance_nonneg

Or via pytest:
    pytest tools/sim/optimaltransport_wasserstein_distance_nonneg.py
"""
from __future__ import annotations

import random

from tools.sim.harness import Strategy, floats, ints, run_harness
from tools.sim.mutations import (
    custom_transform,
    drop_factor,
    swap_inequality,
)


def _draw_vectors(seed: float, n: int, scale: float) -> tuple[list[float], list[float]]:
    """Deterministic per-seed draw of two real vectors in [-scale, scale]^n."""
    rng = random.Random(int(seed * 1e6) % (2**32))
    p = [rng.uniform(-scale, scale) for _ in range(n)]
    q = [rng.uniform(-scale, scale) for _ in range(n)]
    return p, q


def wasserstein_distance_nonneg_spec(seed: float, n: int, scale: float) -> bool:
    """The theorem itself, evaluated numerically.

    Draws two real vectors of length `n` uniformly in `[-scale, scale]`,
    computes the discrete L1 Wasserstein-style cost
    `sum_i |p_i - q_i|`, and returns True when the cost is >= 0.
    The Lean theorem guarantees this for all real-valued p, q.
    """
    p, q = _draw_vectors(seed, n, scale)
    cost = sum(abs(pi - qi) for pi, qi in zip(p, q))
    return cost >= 0.0


# Mutations: standard library wrappers from tools.sim.mutations plus a
# strict-bound custom_transform.


def _strict_lower_bound(seed: float, n: int, scale: float) -> bool:
    """Overconstrained claim: cost >= scale * n. Fails most of the
    time since the expected absolute-difference per coordinate is
    `2 scale / 3` for uniform [-scale, scale], giving expected
    cost ~ (2/3) * scale * n, well below `scale * n`."""
    p, q = _draw_vectors(seed, n, scale)
    cost = sum(abs(pi - qi) for pi, qi in zip(p, q))
    return cost >= scale * n


MUTATIONS = (
    swap_inequality(wasserstein_distance_nonneg_spec, name="swap_inequality"),
    # `drop_factor` pins n=1 in every draw; the spec still passes
    # (any single |p-q| is non-negative), so we instead pin scale=0
    # which makes the spec pass vacuously (cost=0). Use a custom
    # transform that drops the absolute value: sum_i (p_i - q_i)
    # with a positivity demand, which fails ~50% of the time on
    # symmetric uniform draws.
    custom_transform(
        wasserstein_distance_nonneg_spec,
        lambda seed, n, scale: (
            sum(pi - qi for pi, qi in zip(*_draw_vectors(seed, n, scale))) >= 1e-9
        ),
        name="drop_absolute_value",
        min_failure_rate=0.3,
    ),
    custom_transform(
        wasserstein_distance_nonneg_spec,
        _strict_lower_bound,
        name="strict_lower_bound_n_scale",
        min_failure_rate=0.05,
    ),
)


# Parameter ranges:
#   seed: uniform in [0, 1) for RNG seeding
#   n: vector length 1 to 50 atoms
#   scale: amplitude 0.1 to 10.0
STRATEGY = Strategy(
    seed=floats(0.0, 1.0),
    n=ints(1, 50),
    scale=floats(0.1, 10.0),
)


def main() -> int:
    result = run_harness(
        name="optimaltransport.wasserstein_distance_nonneg",
        spec=wasserstein_distance_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_wasserstein_distance_nonneg() -> None:
    result = run_harness(
        name="optimaltransport.wasserstein_distance_nonneg",
        spec=wasserstein_distance_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=500,
        sweep_points=5,
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
