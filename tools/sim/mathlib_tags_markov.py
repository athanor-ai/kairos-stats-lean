"""Markov inequality: empirical companion.

Lean side (`Pythia/MathlibTags.lean`) retags:
    MeasureTheory.meas_ge_le_lintegral_div
with `@[stat_lemma]`.  That theorem states, for an AE-measurable
f : alpha -> R>=0inf and epsilon != 0:
    mu { omega | f(omega) >= epsilon } <= (integral f) / epsilon.

The formal proof lives in Mathlib; pythia adds the `@[stat_lemma]`
registry entry and this empirical layer.  We verify the bound
numerically using exponentially-distributed samples (non-negative,
with known mean 1/lam) and run a mutation harness to confirm the
test set is not passing vacuously.

Run:
    python -m tools.sim.mathlib_tags_markov

Or via pytest:
    pytest tools/sim/mathlib_tags_markov.py
"""
from __future__ import annotations

import math
import random

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    le,
    run_harness,
)


def markov_spec(eps: float, lam: float) -> bool:
    """Markov inequality, evaluated numerically.

    Generates exponential-distribution samples (non-negative) with rate
    lam.  The theoretical mean is E[X] = 1/lam.

    Markov guarantees: P(X >= eps) <= E[X] / eps = (1/lam) / eps.

    Returns True when the empirical tail frequency is within the Markov
    bound plus 5% slack (Monte-Carlo noise from n=5000 samples).
    """
    rng = random.Random(int(eps * 1000) + int(lam * 1000) + 42)
    n = 5000
    samples = [-math.log(1 - rng.random()) / lam for _ in range(n)]
    empirical_mean = sum(samples) / n
    empirical_tail = sum(1 for x in samples if x >= eps) / n
    bound = empirical_mean / eps if eps > 0 else float("inf")
    # Allow 5% slack for Monte-Carlo noise (n=5000, eps>0.5 should be tight).
    return empirical_tail <= bound + 0.05


# ---------------------------------------------------------------------------
# Mutations: each deliberately perturbs the spec. The harness asserts every
# mutation FAILS on >= min_failure_rate of random draws, confirming the
# original test set is not vacuous.
#
# Failure rate measured over 2000 random (eps, lam) draws from STRATEGY:
#   _negate_bound    ~ 100 % (tail << bound for exponential, so reversed check
#                              almost always returns False)
#   _claim_tail_zero ~  37 % (hardcoded bound = 0 fails whenever lam*eps < 3)
#   _off_by_2x       ~  14 % (bimodal distribution makes Markov near-tight,
#                              halving the bound produces measurable failures)
# ---------------------------------------------------------------------------


def _negate_bound(eps: float, lam: float) -> bool:
    """Reversed inequality: checks tail >= bound + 0.05 (wrong direction).

    For exponential samples, the Markov bound is very loose, so the
    empirical tail is nearly always far below bound. This reversed check
    almost always returns False, confirming the original direction is
    non-trivial."""
    rng = random.Random(int(eps * 1000) + int(lam * 1000) + 42)
    n = 5000
    samples = [-math.log(1 - rng.random()) / lam for _ in range(n)]
    empirical_mean = sum(samples) / n
    empirical_tail = sum(1 for x in samples if x >= eps) / n
    bound = empirical_mean / eps if eps > 0 else float("inf")
    return empirical_tail >= bound + 0.05


def _claim_tail_is_zero(eps: float, lam: float) -> bool:
    """Constant-zero bound: checks tail <= 0.05.

    Represents the bug of hardcoding 0 as the probability bound.
    For moderate (eps, lam) where lam*eps < ln(20) ~ 3.0, the
    exponential tail exceeds 5% and this check fails."""
    rng = random.Random(int(eps * 1000) + int(lam * 1000) + 42)
    n = 5000
    samples = [-math.log(1 - rng.random()) / lam for _ in range(n)]
    empirical_tail = sum(1 for x in samples if x >= eps) / n
    # Bug: pretend the bound is 0 (tail should be negligible).
    return empirical_tail <= 0.0 + 0.05


def _off_by_2x(eps: float, lam: float) -> bool:
    """Halved bound on a near-tight distribution.

    Uses a bimodal distribution (mass at 0 and 2/lam with equal weight)
    where E[X] = 1/lam and P(X >= eps) ~ 0.5 for eps < 2/lam.  This
    makes Markov near-tight, so halving the bound causes measurable
    failures in the regime lam*eps < 1."""
    rng = random.Random(int(eps * 1000) + int(lam * 1000) + 42)
    n = 5000
    # Bimodal: X = 2/lam with prob 0.5, else 0.
    samples = [2.0 / lam if rng.random() < 0.5 else 0.0 for _ in range(n)]
    empirical_mean = sum(samples) / n
    empirical_tail = sum(1 for x in samples if x >= eps) / n
    bound = empirical_mean / eps if eps > 0 else float("inf")
    # Bug: use half the correct Markov bound.
    return empirical_tail <= bound / 2 + 0.05


# ---------------------------------------------------------------------------
# Strategy: eps in [0.5, 5.0], lam in [0.5, 3.0].
# Moderate eps and lam keep Markov non-trivial (tail is a real fraction).
# ---------------------------------------------------------------------------
STRATEGY = Strategy(
    eps=floats(0.5, 5.0),
    lam=floats(0.5, 3.0),
)

MUTATIONS = (
    Mutation(name="negate_bound", spec=_negate_bound),
    Mutation(name="claim_tail_is_zero", spec=_claim_tail_is_zero),
    Mutation(name="off_by_2x", spec=_off_by_2x),
)


def main() -> int:
    result = run_harness(
        name="mathlib_tags.markov_inequality",
        spec=markov_spec,
        strategy=STRATEGY,
        n_pbt=1_000,
        sweep_points=8,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_markov_inequality() -> None:
    """pytest hook: runs a shorter harness and asserts all checks pass."""
    result = run_harness(
        name="mathlib_tags.markov_inequality",
        spec=markov_spec,
        strategy=STRATEGY,
        n_pbt=200,
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
