"""Shannon binary entropy non-negativity: empirical companion.

Lean side (`Pythia/InfoTheory/BinaryEntropy.lean::binary_entropy_nonneg`)
proves: `H(p) = -p * log p - (1-p) * log(1-p) >= 0` for all `p` in `[0, 1]`,
with the convention `0 * log 0 = 0` (handled by `Real.negMulLog`).

This module verifies the formal bound numerically across the full unit interval
and runs a mutation harness to confirm the test set is not vacuous.

Run:
    python -m tools.sim.info_theory_binary_entropy

Or via pytest:
    pytest tools/sim/info_theory_binary_entropy.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def _neg_mul_log(x: float) -> float:
    """Compute -x * log(x) with the convention 0 * log(0) = 0."""
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log(x)


def binary_entropy_nonneg_spec(p: float) -> bool:
    """The theorem itself, evaluated numerically.

    Returns True when H(p) = -p*log(p) - (1-p)*log(1-p) >= 0,
    which the Lean theorem guarantees for all p in [0, 1].
    A tiny float slack accounts for rounding at the boundaries.
    """
    H = _neg_mul_log(p) + _neg_mul_log(1 - p)
    return H >= -1e-12


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate(p: float) -> bool:
    """Negated entropy: -(H(p)) >= 0. Fails whenever H(p) > 0."""
    H = _neg_mul_log(p) + _neg_mul_log(1 - p)
    return -H >= 0


def _drop_second_term(p: float) -> bool:
    """Drop second term and subtract 1: -p*log(p) - 1 >= 0. Fails for most p."""
    return _neg_mul_log(p) - 1 >= 0


def _strict_positive(p: float) -> bool:
    """Overconstrained lower bound H(p) >= 0.5. Fails near p=0 or p=1."""
    H = _neg_mul_log(p) + _neg_mul_log(1 - p)
    return H >= 0.5


STRATEGY = Strategy(p=floats(0.0, 1.0))

MUTATIONS = (
    Mutation(name="negate", spec=_negate),
    Mutation(name="drop_second_term", spec=_drop_second_term),
    Mutation(name="strict_positive", spec=_strict_positive),
)


def main() -> int:
    result = run_harness(
        name="info_theory.binary_entropy_nonneg",
        spec=binary_entropy_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=20,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_binary_entropy_nonneg() -> None:
    result = run_harness(
        name="info_theory.binary_entropy_nonneg",
        spec=binary_entropy_nonneg_spec,
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
        f"vacuous-test risk: mutations missed = {result.mutations_missed}"
    )


if __name__ == "__main__":
    import sys
    sys.exit(main())
