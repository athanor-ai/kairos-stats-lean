"""Smoke test: a full Sim declaration exercising all 7 v2 components.

The theorem is the trivial identity x + 0 = x over reals.
This test verifies the harness composes end-to-end without errors.

Lean backing (informational — lake skips gracefully if absent):
    theorem add_zero_real (x : Float) : x + 0 == x := by native_decide
"""
from __future__ import annotations

import math

import hypothesis.strategies as st
import pytest

from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2.differential import DifferentialCheck
from tools.sim.harness.v2.generators import real_in
from tools.sim.harness.v2.metamorphic import limit_case, homogeneous
from tools.sim.harness.v2.properties import identity


# ─── property ────────────────────────────────────────────────────────


def _identity_prop(x: float) -> bool:
    """x + 0.0 == x within floating-point tolerance."""
    return identity(
        lhs_fn=lambda x: x + 0.0,
        rhs_fn=lambda x: x,
        inputs={"x": x},
        tolerance=1e-12,
    )


# ─── symmetry: homogeneous degree 1 (scaling x scales result) ────────
# f(c * x) = c^1 * f(x) where f(x) = x + 0 = x

_homogeneous_sym = homogeneous(
    fn=lambda x: x + 0.0,
    arg_names=["x"],
    factor_strategy=real_in(0.1, 5.0),
    exponent=1,
    base_strategy=st.fixed_dictionaries({"x": real_in(0.1, 100.0)}),
    max_examples=50,
)

# ─── symmetry: limit case at x=0 ─────────────────────────────────────

_limit_sym = limit_case(
    fn=lambda x: x + 0.0,
    arg="x",
    limit_value=0.0,
    expected_form_fn=lambda x: 0.0,
    base_strategy=st.fixed_dictionaries({"x": real_in(-100.0, 100.0)}),
    max_examples=30,
)

# ─── differential check — skips gracefully when lake absent ──────────

_diff_check = DifferentialCheck(
    lean_decl="{x} + 0",
    python_fn=lambda x: x + 0.0,
    inputs={"x": 42.0},
    tolerance=1e-9,
)

# ─── full Sim declaration ─────────────────────────────────────────────

_smoke_sim = Sim(
    name="smoke.identity_add_zero",
    lean_module="Pythia.Smoke.AddZero",
    generator=real_in(-1e6, 1e6),
    property=_identity_prop,
    symmetries=[_homogeneous_sym, _limit_sym],
    differential=_diff_check,
    boundary_targets=["x"],
    replications=200,
    statistical_assertion={"claimed_prob": 0.01, "ci_level": 0.99},
)


# ─── pytest entry points ──────────────────────────────────────────────


def test_smoke_sim_runs() -> None:
    """The smoke Sim should compose and run end-to-end without errors."""
    _smoke_sim.run()


def test_smoke_sim_property_alone() -> None:
    """Property check passes on a range of trivial inputs."""
    for x in [0.0, 1.0, -1.0, 1e9, -1e9, math.pi, -math.pi]:
        assert _identity_prop(x), f"identity_prop failed at x={x}"


def test_smoke_differential_skip_when_no_lake() -> None:
    """If lake is absent the differential check skips (returns True)."""
    import tools.sim.harness.v2.differential as diff_mod

    original = diff_mod.shutil.which

    def no_lake(cmd):
        if cmd == "lake":
            return None
        return original(cmd)

    diff_mod.shutil.which = no_lake
    try:
        sim = Sim(
            name="smoke.diff_skip_test",
            lean_module="Pythia.Smoke",
            generator=real_in(0.0, 1.0),
            property=lambda x: True,
            differential=DifferentialCheck(
                lean_decl="{x}",
                python_fn=lambda x: x,
                inputs={"x": 1.0},
            ),
            replications=10,
        )
        sim.run()  # should not raise
    finally:
        diff_mod.shutil.which = original
