"""ATH-791 PoC: v2 Hardy-Weinberg sim + bug-injection demo.

Four tests prove two things:
  1. The v2 Sim runs correctly on the true spec.
  2. v2's deterministic ``limit_case(arg="p", limit_value=0.5)``
     catches a point-perturbation bug that v1 PBT misses.

Bug design: the buggy spec adds +0.001 ONLY when p == 0.5 exactly.
v1 samples p uniformly from [0.0, 1.0] — probability zero of hitting
0.5 exactly, so it passes the bug every run.
v2 limit_case forces p=0.5 deterministically on every example,
catching the +0.001 deviation against the tolerance=1e-9 guard.
"""
from __future__ import annotations

import math
import random

import pytest

from tools.sim.harness import run_harness, Strategy, floats
from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2.generators import real_in
from tools.sim.harness.v2.metamorphic import limit_case
from tools.sim.harness.v2.properties import identity
from tools.sim.harness.v2 import replay as replay_mod

from tools.sim.v2_biology_hardy_weinberg import (
    hardy_weinberg_v2,
    _hw_lhs,
    _GENERATOR,
)


# ── Buggy spec (lives only in this test file) ─────────────────────────────

def hw_buggy(p: float) -> float:
    """Buggy HW sum: correct everywhere EXCEPT p == 0.5 exactly.

    At p=0.5 it adds +0.001.  v1 PBT on continuous [0,1] hits 0.5
    with probability zero.  v2 limit_case(arg="p", limit_value=0.5)
    hits it every run.
    """
    q = 1.0 - p
    if abs(p - 0.5) < 1e-12:
        return p ** 2 + 2 * p * q + q ** 2 + 0.001
    return p ** 2 + 2 * p * q + q ** 2


def _buggy_property(sample: dict) -> bool:
    """Property check using the buggy spec (v2 interface)."""
    return identity(
        lhs_fn=lambda p: hw_buggy(p),
        rhs_fn=lambda p: 1.0,
        inputs=sample,
        tolerance=1e-9,
    )


def _buggy_spec_v1(p: float) -> bool:
    """v1-compatible wrapper for run_harness."""
    return math.isclose(hw_buggy(p), 1.0, rel_tol=1e-9, abs_tol=1e-9)


# ── helpers ───────────────────────────────────────────────────────────────

def _make_buggy_v2_sim(name: str) -> Sim:
    """Build a v2 Sim with the buggy spec wired as the property.

    The limit_case symmetry forces p=0.5 and compares hw_buggy(0.5)
    to the expected constant 1.0.  The +0.001 spike is well above
    tolerance=1e-9.
    """
    # Symmetry: at p=0.5, limit_case probes deterministically.
    # This is the mechanism that catches the bug every run.
    buggy_limit_sym = limit_case(
        fn=hw_buggy,
        arg="p",
        limit_value=0.5,
        expected_form_fn=lambda p: 1.0,
        base_strategy=_GENERATOR,
        tolerance=1e-9,   # +0.001 >> 1e-9, so this catches the bug
        max_examples=10,  # deterministic: all 10 samples at p=0.5
    )
    return Sim(
        name=name,
        lean_module="Pythia.Bio.Population",
        generator=_GENERATOR,
        property=_buggy_property,
        symmetries=[buggy_limit_sym],
        replications=500,
    )


# ── tests ─────────────────────────────────────────────────────────────────


def test_v2_correct_spec_passes(isolated_ce_dir) -> None:
    """v2 Sim with the CORRECT spec runs without raising.

    Uses the canonical ``hardy_weinberg_v2`` declaration from
    tools/sim/v2_biology_hardy_weinberg.py.
    """
    hardy_weinberg_v2.run()


def test_v1_misses_buggy_spec() -> None:
    """v1 PBT passes the buggy spec — DEMONSTRATES the v1 hole.

    v1 samples p uniformly from [0.0, 1.0] using a pseudo-random
    generator seeded to 42.  The probability of drawing p=0.5 exactly
    from a continuous uniform distribution is zero, so the +0.001
    spike is never triggered.

    The v1 harness should report ``pbt_passed=True`` and
    ``sweep_passed=True`` (v1 sweep linspace endpoints don't include
    exactly 0.5 for small sweep_points).
    """
    v1_strategy = Strategy(p=floats(0.0, 1.0))
    result = run_harness(
        name="bio.hardy_weinberg_buggy.v1_misses",
        spec=_buggy_spec_v1,
        strategy=v1_strategy,
        n_pbt=2_000,   # same as v1 CI run in original sim
        sweep_points=4,  # linspace: 0.0, 0.333, 0.667, 1.0 — no 0.5
        seed=42,
    )
    # v1 must NOT raise — it passes the bug.
    assert result.pbt_passed, (
        "unexpected: v1 PBT caught the buggy spec — "
        "adjust the bug design so the limit point is not in the sweep grid"
    )
    assert result.sweep_passed, (
        "unexpected: v1 sweep caught the buggy spec — "
        "the sweep grid accidentally included p=0.5"
    )


def test_v2_catches_buggy_spec(isolated_ce_dir) -> None:
    """v2 limit_case(arg="p", limit_value=0.5) raises AssertionError.

    The limit_case symmetry forces p=0.5 on every example.  The buggy
    spec returns 1.001 there vs expected 1.0, which fails the
    tolerance=1e-9 guard — so the assertion fires every run.
    """
    buggy_sim = _make_buggy_v2_sim(
        "bio.hardy_weinberg_buggy.v2_catches"
    )
    with pytest.raises(AssertionError):
        buggy_sim.run()


def test_buggy_spec_passes_at_random_p() -> None:
    """Sanity: the bug is genuinely limit-only.

    Sample 100 random p values from (0.0, 1.0) excluding a small
    neighbourhood of 0.5.  The buggy spec must return the same value
    as the correct spec at all of them, proving the +0.001 spike is
    confined to p=0.5 exactly.
    """
    rng = random.Random(0xCAFEBABE)
    n_tested = 0
    for _ in range(100):
        # Draw p away from 0.5 (exclude [0.499, 0.501])
        p = rng.uniform(0.0, 0.499)
        assert math.isclose(hw_buggy(p), _hw_lhs(p), rel_tol=1e-12, abs_tol=1e-12), (
            f"buggy spec deviated at p={p} (expected deviation only at 0.5)"
        )
        p2 = rng.uniform(0.501, 1.0)
        assert math.isclose(hw_buggy(p2), _hw_lhs(p2), rel_tol=1e-12, abs_tol=1e-12), (
            f"buggy spec deviated at p={p2} (expected deviation only at 0.5)"
        )
        n_tested += 2
    assert n_tested == 200, "sanity: expected 200 samples"


# ── conftest fixture ──────────────────────────────────────────────────────

@pytest.fixture
def isolated_ce_dir(tmp_path, monkeypatch):
    """Redirect counterexample writes to a temp directory."""
    monkeypatch.setattr(replay_mod, "_CE_DIR", tmp_path / "counterexamples")
    return tmp_path / "counterexamples"
