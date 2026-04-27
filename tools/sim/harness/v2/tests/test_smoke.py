"""Smoke test: a Sim declaration exercising every v2 component.

The theorem is the trivial identity ``x + 0 == x`` over reals.
This test verifies the harness composes end-to-end. It is the
contract that a v2 ``Sim`` runs through:

* ``_run_property`` — exercised under both strict and statistical
  modes (two ``Sim`` instances).
* ``_run_symmetries`` — homogeneous + limit_case.
* ``_run_differential`` — skips gracefully when ``lake`` absent.
* coverage targeting — generator wrapped via ``target_extreme``;
  ``Sim._run_property_strict`` reads ``_v2_edge_fn`` and calls
  ``hypothesis.target()``.
* counterexample replay — ``replay_corpus`` runs with the same
  shape as ``record_failure`` saves.

Lean backing (informational — lake skips gracefully if absent):
    theorem add_zero_real (x : Float) : x + 0 == x := by native_decide
"""
from __future__ import annotations

import math

import hypothesis.strategies as st

from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2.differential import DifferentialCheck
from tools.sim.harness.v2.generators import real_in
from tools.sim.harness.v2.metamorphic import limit_case, homogeneous
from tools.sim.harness.v2.properties import identity
from tools.sim.harness.v2.targeting import target_extreme


# Property: x + 0 == x within float tolerance.
def _identity_prop(x: float) -> bool:
    return identity(
        lhs_fn=lambda x: x + 0.0,
        rhs_fn=lambda x: x,
        inputs={"x": x},
        tolerance=1e-12,
    )


# Symmetry: f(c * x) = c^1 * f(x) where f(x) = x.
_homogeneous_sym = homogeneous(
    fn=lambda x: x + 0.0,
    arg_names=["x"],
    factor_strategy=real_in(0.1, 5.0),
    exponent=1,
    base_strategy=st.fixed_dictionaries({"x": real_in(0.1, 100.0)}),
    max_examples=50,
)

# Symmetry: at x=0, f reduces to 0.
_limit_sym = limit_case(
    fn=lambda x: x + 0.0,
    arg="x",
    limit_value=0.0,
    expected_form_fn=lambda x: 0.0,
    base_strategy=st.fixed_dictionaries({"x": real_in(-100.0, 100.0)}),
    max_examples=30,
)

# Differential: lean #eval matches python within tolerance.
_diff_check = DifferentialCheck(
    lean_decl="{x} + 0",
    python_fn=lambda x: x + 0.0,
    inputs={"x": 42.0},
    tolerance=1e-9,
)

# Generator wrapped in target_extreme so coverage targets large |x|.
# This is the path that exercises the targeting subsystem end-to-end:
# ``Sim._run_property_strict`` reads ``_v2_edge_fn`` from this strategy
# and calls ``hypothesis.target(edge_fn(sample))`` inside ``@given``.
_targeted_generator = target_extreme(
    real_in(-1e6, 1e6),
    edge_fn=lambda x: abs(x),
)


# Strict-mode Sim: any property failure raises immediately.
_smoke_sim_strict = Sim(
    name="smoke.identity_add_zero.strict",
    lean_module="Pythia.Smoke.AddZero",
    generator=_targeted_generator,
    property=_identity_prop,
    symmetries=[_homogeneous_sym, _limit_sym],
    differential=_diff_check,
    replications=200,
)


# Statistical-mode Sim: count violations across N draws, assert
# upper Wilson CI bound on the violation rate <= claimed_prob. For
# this trivial identity the violation rate is zero so the assertion
# trivially holds.
_smoke_sim_statistical = Sim(
    name="smoke.identity_add_zero.statistical",
    lean_module="Pythia.Smoke.AddZero",
    generator=real_in(-1e3, 1e3),
    property=_identity_prop,
    replications=200,
    statistical_assertion={"claimed_prob": 0.05, "ci_level": 0.99},
)


# ─── pytest entry points ──────────────────────────────────────────────


def test_smoke_strict_runs() -> None:
    """The strict-mode smoke Sim composes and runs end-to-end."""
    _smoke_sim_strict.run()


def test_smoke_statistical_runs() -> None:
    """The statistical-mode smoke Sim composes and runs end-to-end."""
    _smoke_sim_statistical.run()


def test_smoke_property_alone() -> None:
    """The identity property holds on a representative sample."""
    for x in [0.0, 1.0, -1.0, 1e9, -1e9, math.pi, -math.pi]:
        assert _identity_prop(x), f"identity_prop failed at x={x}"


def test_smoke_differential_skip_when_no_lake() -> None:
    """If lake is absent the differential check skips silently."""
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
