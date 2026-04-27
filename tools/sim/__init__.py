"""Pythia simulation harness — Python-side empirical verification.

Companion to the Lean theorems under `Pythia/<Domain>/*.lean`. Every
theorem we ship in pythia comes with a Lean kernel-checked proof
(layer 0) AND a Python simulation harness (layer 1) that runs:

  * Hypothesis-style property-based test draws (zero-dep RNG)
  * Deterministic parameter sweep over realistic ranges
  * Mutation testing: deliberately-wrong specs that the harness
    expects to catch (vacuous-test guard)

Lean stays a proof assistant. Python owns numerics. No simulation
primitives in Lean.

Public API:

    from tools.sim import HarnessResult, Strategy, run_harness

License: Apache-2.0 (same as the rest of pythia).
"""
from __future__ import annotations

from .harness import (
    HarnessResult,
    Mutation,
    Strategy,
    run_harness,
)

__all__ = [
    "HarnessResult",
    "Mutation",
    "Strategy",
    "run_harness",
]
