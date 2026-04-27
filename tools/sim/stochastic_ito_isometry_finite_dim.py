"""Discrete Itô isometry (Cauchy-Schwarz form): empirical companion.

Lean side (`Pythia/Stochastic/ItoIsometryFiniteDim.lean::ito_isometry_finite_dim`)
proves: `(sum_i f_i)^2 <= n * sum_i (f_i)^2` for any `f : Fin n -> R`.

This module verifies the formal bound numerically across realistic
parameter ranges (vector lengths 1 to 50, amplitudes 0.1 to 10) and
runs a mutation harness to confirm the test set is not vacuous.

Run:
    python -m tools.sim.stochastic_ito_isometry_finite_dim

Or via pytest:
    pytest tools/sim/stochastic_ito_isometry_finite_dim.py
"""
from __future__ import annotations

import random

from tools.sim.harness import Strategy, floats, ints, run_harness
from tools.sim.mutations import (
    custom_transform,
    drop_factor,
    swap_inequality,
)


def _draw_f(seed: float, n: int, scale: float) -> list[float]:
    """Deterministic per-seed real vector in [-scale, scale]^n."""
    rng = random.Random(int(seed * 1e6) % (2**32))
    return [rng.uniform(-scale, scale) for _ in range(n)]


def ito_isometry_finite_dim_spec(seed: float, n: int, scale: float) -> bool:
    """The theorem itself, evaluated numerically.

    Computes `lhs = (sum f_i)^2` and `rhs = n * sum (f_i)^2`. Returns
    True when `lhs <= rhs` (with float slack); the Lean theorem
    guarantees this for all real-valued f. This is exactly the
    discrete Cauchy-Schwarz bound underlying the Itô isometry in
    finite dimension.
    """
    f = _draw_f(seed, n, scale)
    lhs = sum(f) ** 2
    rhs = n * sum(x * x for x in f)
    # Equality case is when f is constant; allow tiny float slack.
    return lhs <= rhs + 1e-9 * max(1.0, abs(rhs))


# Mutations: standard library wrappers from tools.sim.mutations plus a
# strict-bound custom_transform.


def _drop_n_factor(seed: float, n: int, scale: float) -> bool:
    """Drop the `n` factor on the RHS: `(sum f)^2 <= sum f^2`. This
    is exactly the Cauchy-Schwarz bound without the cardinality
    multiplier. For uniform [-scale, scale] draws we have
    `E[(sum f)^2] = n*var = n*scale^2/3` while
    `E[sum f^2] = n*scale^2/3`; the LHS exceeds the RHS roughly half
    the time (driven by the constant-direction projection), so the
    mutation is detectable."""
    f = _draw_f(seed, n, scale)
    lhs = sum(f) ** 2
    rhs = sum(x * x for x in f)
    return lhs <= rhs


def _drop_square_rhs(seed: float, n: int, scale: float) -> bool:
    """Drop the square on the RHS: (sum f)^2 <= n * sum f. Fails for
    most draws where sum f is small and (sum f)^2 is positive."""
    f = _draw_f(seed, n, scale)
    lhs = sum(f) ** 2
    rhs = n * sum(f)
    return lhs <= rhs


MUTATIONS = (
    swap_inequality(ito_isometry_finite_dim_spec, name="swap_inequality"),
    custom_transform(
        ito_isometry_finite_dim_spec,
        _drop_n_factor,
        name="drop_n_factor",
        min_failure_rate=0.05,
    ),
    custom_transform(
        ito_isometry_finite_dim_spec,
        _drop_square_rhs,
        name="drop_square_rhs",
        min_failure_rate=0.3,
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
        name="stochastic.ito_isometry_finite_dim",
        spec=ito_isometry_finite_dim_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_ito_isometry_finite_dim() -> None:
    result = run_harness(
        name="stochastic.ito_isometry_finite_dim",
        spec=ito_isometry_finite_dim_spec,
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
