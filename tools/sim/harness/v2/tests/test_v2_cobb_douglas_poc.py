"""ATH-791 PoC: v2 Cobb-Douglas sim + bug-injection demo.

Four tests prove two things:
  1. The v2 Sim runs correctly on the true spec.
  2. v2's deterministic ``limit_case(arg="alpha", limit_value=0.5)``
     catches a point-perturbation bug that v1 PBT misses.

Bug design: the buggy spec adds +0.001 ONLY when alpha == 0.5 exactly.
v1 samples alpha uniformly from [0.05, 0.95] — probability zero of
hitting 0.5 exactly, so it passes the bug every run.
v2 limit_case forces alpha=0.5 deterministically on every example,
catching the +0.001 deviation against the tolerance=1e-6 guard.
"""
from __future__ import annotations

import math
import random

import hypothesis.strategies as st
import pytest

from tools.sim.harness import run_harness, Strategy, floats
from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2.generators import positive_real, real_in
from tools.sim.harness.v2.metamorphic import homogeneous, limit_case
from tools.sim.harness.v2.properties import identity
from tools.sim.harness.v2 import replay as replay_mod

from tools.sim.v2_economics_cobb_douglas import (
    cobb_douglas_v2,
    _cobb_douglas_lhs,
    _cobb_douglas_rhs,
    _GENERATOR,
)


# ── Buggy spec (lives only in this test file) ─────────────────────────────

def cobb_douglas_buggy(K: float, L: float, lam: float, alpha: float) -> float:
    """Buggy LHS: returns the correct value UNLESS alpha == 0.5 exactly,
    where it adds +0.001.  v1 PBT (continuous uniform on alpha) hits
    alpha=0.5 with probability zero — it never catches this bug.
    v2 limit_case(arg="alpha", limit_value=0.5) hits it every run.
    """
    if abs(alpha - 0.5) < 1e-12:
        return (lam * K) ** alpha * (lam * L) ** (1 - alpha) + 0.001
    return (lam * K) ** alpha * (lam * L) ** (1 - alpha)


def _buggy_property(sample: dict) -> bool:
    """Property check using the buggy LHS."""
    return identity(
        lhs_fn=cobb_douglas_buggy,
        rhs_fn=_cobb_douglas_rhs,
        inputs=sample,
        tolerance=1e-9,
    )


def _buggy_spec_v1(K: float, L: float, lam: float, alpha: float) -> bool:
    """v1-compatible wrapper: returns bool directly (for run_harness)."""
    lhs = cobb_douglas_buggy(K, L, lam, alpha)
    rhs = _cobb_douglas_rhs(K, L, lam, alpha)
    return math.isclose(lhs, rhs, rel_tol=1e-9, abs_tol=1e-9)


# ── helpers ───────────────────────────────────────────────────────────────

def _make_buggy_v2_sim(name: str) -> Sim:
    """Build a v2 Sim with the buggy spec wired as the property.

    The limit_case symmetry forces alpha=0.5 and compares the buggy
    LHS to the correct RHS — the +0.001 is well above tolerance=1e-6.
    """
    # Symmetry: at alpha=0.5, limit_case probes deterministically.
    # This is the mechanism that catches the bug every run.
    buggy_limit_sym = limit_case(
        fn=cobb_douglas_buggy,
        arg="alpha",
        limit_value=0.5,
        expected_form_fn=_cobb_douglas_rhs,
        base_strategy=_GENERATOR,
        tolerance=1e-6,   # +0.001 >> 1e-6, so this catches the bug
        max_examples=10,  # deterministic: 10 samples all at alpha=0.5
    )
    return Sim(
        name=name,
        lean_module="Pythia.Economics.CobbDouglas",
        generator=_GENERATOR,
        property=_buggy_property,
        symmetries=[buggy_limit_sym],
        replications=500,
    )


# ── tests ─────────────────────────────────────────────────────────────────


def test_v2_correct_spec_passes(isolated_ce_dir) -> None:
    """v2 Sim with the CORRECT spec runs without raising.

    Uses the canonical ``cobb_douglas_v2`` declaration from
    tools/sim/v2_economics_cobb_douglas.py.
    """
    cobb_douglas_v2.run()


def test_v1_misses_buggy_spec() -> None:
    """v1 PBT passes the buggy spec — DEMONSTRATES the v1 hole.

    v1 samples alpha uniformly from [0.05, 0.95] using a pseudo-random
    generator seeded to 42.  The probability of drawing alpha=0.5
    exactly from a continuous uniform distribution is zero, so the
    +0.001 spike at alpha=0.5 is never exercised.

    The v1 harness should report ``pbt_passed=True`` and
    ``sweep_passed=True`` (v1 sweep uses linspace endpoints, not 0.5).
    """
    # v1 Strategy mirrors the original sim's STRATEGY.
    v1_strategy = Strategy(
        K=floats(1e-2, 1e6, log_scale=True),
        L=floats(1e-2, 1e6, log_scale=True),
        lam=floats(1e-2, 100.0, log_scale=True),
        alpha=floats(0.05, 0.95),
    )
    result = run_harness(
        name="economics.cobb_douglas_buggy.v1_misses",
        spec=_buggy_spec_v1,
        strategy=v1_strategy,
        n_pbt=2_000,   # same as v1 CI run in original sim
        sweep_points=4,
        seed=42,
    )
    # v1 must NOT raise — it passes the bug.
    # (If this assertion fails, the v1 hole no longer exists; update the demo.)
    assert result.pbt_passed, (
        "unexpected: v1 PBT caught the buggy spec — "
        "adjust the bug design so the limit point is not in the sweep grid"
    )
    assert result.sweep_passed, (
        "unexpected: v1 sweep caught the buggy spec — "
        "the sweep grid accidentally hit alpha=0.5"
    )


def test_v2_catches_buggy_spec(isolated_ce_dir) -> None:
    """v2 limit_case(arg="alpha", limit_value=0.5) raises AssertionError.

    The limit_case symmetry forces alpha=0.5 on every example.  The
    buggy LHS returns correct_value + 0.001 there, which fails the
    tolerance=1e-6 guard — so the assertion fires every run.
    """
    buggy_sim = _make_buggy_v2_sim(
        "economics.cobb_douglas_buggy.v2_catches"
    )
    with pytest.raises(AssertionError):
        buggy_sim.run()


def test_buggy_spec_passes_at_random_alpha() -> None:
    """Sanity: the bug is genuinely limit-only.

    Sample 100 random alpha values from (0.05, 0.95) excluding a
    neighbourhood of 0.5.  The buggy spec must return the same value
    as the correct spec at all of them, proving the +0.001 spike is
    confined to alpha=0.5 exactly.
    """
    rng = random.Random(0xDEADBEEF)
    K, L, lam = 2.0, 3.0, 1.5
    n_tested = 0
    for _ in range(100):
        # Draw alpha away from 0.5 (exclude [0.49, 0.51])
        alpha = rng.uniform(0.05, 0.49)
        buggy = cobb_douglas_buggy(K, L, lam, alpha)
        correct = _cobb_douglas_lhs(K, L, lam, alpha)
        assert math.isclose(buggy, correct, rel_tol=1e-12, abs_tol=1e-12), (
            f"buggy spec deviated at alpha={alpha} (expected deviation only at 0.5)"
        )
        n_tested += 1
        # Also draw from the upper half
        alpha2 = rng.uniform(0.51, 0.95)
        buggy2 = cobb_douglas_buggy(K, L, lam, alpha2)
        correct2 = _cobb_douglas_lhs(K, L, lam, alpha2)
        assert math.isclose(buggy2, correct2, rel_tol=1e-12, abs_tol=1e-12), (
            f"buggy spec deviated at alpha={alpha2} (expected deviation only at 0.5)"
        )
        n_tested += 1
    assert n_tested == 200, "sanity: expected 200 samples"


# ── conftest fixture re-used from sibling tests ───────────────────────────

@pytest.fixture
def isolated_ce_dir(tmp_path, monkeypatch):
    """Redirect counterexample writes to a temp directory."""
    monkeypatch.setattr(replay_mod, "_CE_DIR", tmp_path / "counterexamples")
    return tmp_path / "counterexamples"
