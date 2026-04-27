"""Signal energy non-negativity: empirical companion.

Lean side (`Pythia/Engineering/SignalEnergy.lean::signal_energy_nonneg`)
proves: `sum_i (x i)^2 >= 0` for any discrete-time signal `x : Fin n -> R`.

This module verifies the formal bound numerically across realistic
parameter ranges (signals of length 1 to 100 samples, amplitudes 0.1 to 10)
and runs a mutation harness to confirm the test set is not vacuous.

Run:
    python -m tools.sim.engineering_signal_energy

Or via pytest:
    pytest tools/sim/engineering_signal_energy.py
"""
from __future__ import annotations

import math
import random

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    ints,
    run_harness,
)


def signal_energy_nonneg_spec(seed: float, n: int, scale: float) -> bool:
    """The theorem itself, evaluated numerically.

    Generates `n` samples uniform in `[-scale, scale]`, computes the
    sum of squares, and returns True when the energy is >= 0.
    The Lean theorem guarantees this for all inputs.
    """
    rng = random.Random(int(seed * 1e6) % (2**32))
    samples = [rng.uniform(-scale, scale) for _ in range(n)]
    energy = sum(s * s for s in samples)
    return energy >= 0.0


# Mutations: each one perturbs the spec slightly. The harness asserts
# every mutation FAILS on >= min_failure_rate of random draws,
# confirming the original test set is not vacuous.


def _negate_energy(seed: float, n: int, scale: float) -> bool:
    """Negated energy: -(sum of squares) >= 0. Fails whenever any sample is non-zero."""
    rng = random.Random(int(seed * 1e6) % (2**32))
    samples = [rng.uniform(-scale, scale) for _ in range(n)]
    return -(sum(s * s for s in samples)) >= 0.0


def _drop_square(seed: float, n: int, scale: float) -> bool:
    """Unsigned sum: sum(s) >= 0 instead of sum(s^2) >= 0.
    Passes when the sum is positive but fails roughly half the time on
    uniform zero-mean distributions."""
    rng = random.Random(int(seed * 1e6) % (2**32))
    samples = [rng.uniform(-scale, scale) for _ in range(n)]
    return sum(s for s in samples) >= 0.0


def _strict_lower_bound(seed: float, n: int, scale: float) -> bool:
    """Overconstrained claim: energy >= scale^2 * n.
    Fails most of the time since uniform variance is scale^2/3,
    so the expected energy is scale^2*n/3, well below scale^2*n."""
    rng = random.Random(int(seed * 1e6) % (2**32))
    samples = [rng.uniform(-scale, scale) for _ in range(n)]
    energy = sum(s * s for s in samples)
    return energy >= scale * scale * n


# Parameter ranges:
#   seed: uniform in [0, 1) for RNG seeding
#   n: signal length 1 to 100 samples
#   scale: amplitude 0.1 to 10.0
STRATEGY = Strategy(
    seed=floats(0.0, 1.0),
    n=ints(1, 100),
    scale=floats(0.1, 10.0),
)

MUTATIONS = (
    Mutation(name="negate_energy", spec=_negate_energy),
    Mutation(name="drop_square", spec=_drop_square),
    Mutation(name="strict_lower_bound", spec=_strict_lower_bound),
)


def main() -> int:
    result = run_harness(
        name="engineering.signal_energy_nonneg",
        spec=signal_energy_nonneg_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=5,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


# pytest hook: if pytest discovers this file, it runs the harness as a
# standard test. Pass when the harness reports all_passed.
def test_signal_energy_nonneg() -> None:
    result = run_harness(
        name="engineering.signal_energy_nonneg",
        spec=signal_energy_nonneg_spec,
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
        f"vacuous-test risk: mutations missed = {result.mutations_missed}"
    )


if __name__ == "__main__":
    import sys
    sys.exit(main())
