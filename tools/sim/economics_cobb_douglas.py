"""Cobb-Douglas constant returns to scale — empirical companion.

Lean side (`Pythia/Economics/CobbDouglas.lean::cobb_douglas_crts`)
proves: `(λK)^α · (λL)^(1-α) = λ · K^α · L^(1-α)` for all positive
`K, L, λ` and `α ∈ ℝ`.

This module verifies the formal bound numerically across realistic
parameter ranges + runs a mutation harness to confirm the test set
isn't passing vacuously.

Run:
    python -m tools.sim.economics_cobb_douglas

Or via pytest:
    pytest tools/sim/economics_cobb_douglas.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    isclose,
    run_harness,
)


def cobb_douglas_crts_spec(K: float, L: float, lam: float, alpha: float) -> bool:
    """The theorem itself, evaluated numerically:

        (λK)^α · (λL)^(1-α) == λ · (K^α · L^(1-α))

    Returns True when the equality holds within rtol=1e-9.
    """
    lhs = (lam * K) ** alpha * (lam * L) ** (1 - alpha)
    rhs = lam * (K ** alpha * L ** (1 - alpha))
    return isclose(lhs, rhs, rtol=1e-9)


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of the random draws —
# if any mutation passes, the original test set is vacuous.

def _alpha_off_by_a_tenth(K: float, L: float, lam: float, alpha: float) -> bool:
    """Wrong exponent: bump α by 0.1 in the first factor only."""
    lhs = (lam * K) ** (alpha + 0.1) * (lam * L) ** (1 - alpha)
    rhs = lam * (K ** alpha * L ** (1 - alpha))
    return isclose(lhs, rhs, rtol=1e-9)


def _drop_lambda_scaling(K: float, L: float, lam: float, alpha: float) -> bool:
    """Forget that the LHS scales by λ: drop the λ on the L factor."""
    lhs = (lam * K) ** alpha * L ** (1 - alpha)
    rhs = lam * (K ** alpha * L ** (1 - alpha))
    return isclose(lhs, rhs, rtol=1e-9)


def _wrong_returns_to_scale_factor(
    K: float, L: float, lam: float, alpha: float,
) -> bool:
    """Claim λ² instead of λ on the RHS — increasing returns to scale,
    not constant."""
    lhs = (lam * K) ** alpha * (lam * L) ** (1 - alpha)
    rhs = lam ** 2 * (K ** alpha * L ** (1 - alpha))
    return isclose(lhs, rhs, rtol=1e-9)


# Realistic parameter ranges:
#   K, L  : capital + labour, geometric scale 1e-2 to 1e6 (covers
#           household-scale to multinational-scale firms)
#   lam   : scaling factor, geometric scale 1e-2 to 100 (10 OOM)
#   alpha : capital share, in (0, 1) per Cobb-Douglas convention
STRATEGY = Strategy(
    K=floats(1e-2, 1e6, log_scale=True),
    L=floats(1e-2, 1e6, log_scale=True),
    lam=floats(1e-2, 100.0, log_scale=True),
    alpha=floats(0.05, 0.95),
)

MUTATIONS = (
    Mutation(name="alpha_off_by_0.1", spec=_alpha_off_by_a_tenth),
    Mutation(name="drop_lambda_on_L", spec=_drop_lambda_scaling),
    Mutation(name="returns_factor_lam_squared", spec=_wrong_returns_to_scale_factor),
)


def main() -> int:
    result = run_harness(
        name="economics.cobb_douglas_crts",
        spec=cobb_douglas_crts_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_cobb_douglas_crts() -> None:
    result = run_harness(
        name="economics.cobb_douglas_crts",
        spec=cobb_douglas_crts_spec,
        strategy=STRATEGY,
        n_pbt=2_000,  # smaller for CI; main() uses 10k
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
