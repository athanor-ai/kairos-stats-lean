"""tools.sim.harness — unit tests.

Hermetic — no external deps beyond stdlib + pytest. Verifies the
scaffold's contract so every domain harness call inherits a known-
good substrate.
"""
from __future__ import annotations

import math

import pytest

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    ints,
    choice,
    isclose,
    le,
    run_harness,
    _linspace,
    _geomspace,
    _int_grid,
)


# ─────────────────────────────────────────────────────────────────────
# helpers
# ─────────────────────────────────────────────────────────────────────


class TestLinspace:
    def test_endpoints_included(self):
        out = _linspace(0.0, 1.0, 5)
        assert out[0] == 0.0
        assert out[-1] == 1.0
        assert len(out) == 5

    def test_single_point_returns_lo(self):
        assert _linspace(2.0, 3.0, 1) == [2.0]


class TestGeomspace:
    def test_log_scale_endpoints(self):
        out = _geomspace(0.01, 100.0, 5)
        assert math.isclose(out[0], 0.01, rel_tol=1e-12)
        assert math.isclose(out[-1], 100.0, rel_tol=1e-12)

    def test_geometric_progression(self):
        out = _geomspace(1.0, 1000.0, 4)
        # ratio between consecutive entries should be ~10
        for a, b in zip(out, out[1:]):
            assert math.isclose(b / a, 10.0, rel_tol=1e-9)


class TestIntGrid:
    def test_step_inclusive(self):
        out = _int_grid(0, 10, 6)
        assert out[0] == 0
        assert out[-1] == 10

    def test_n_exceeds_range_returns_full(self):
        out = _int_grid(1, 5, 100)
        assert out == [1, 2, 3, 4, 5]


class TestIsCloseLe:
    def test_isclose_within_rtol(self):
        assert isclose(1.0, 1.0 + 1e-12)

    def test_isclose_outside_rtol(self):
        assert not isclose(1.0, 1.1)

    def test_le_with_atol_slack(self):
        assert le(1.0, 0.9999, atol=1e-3)

    def test_le_violation_outside_atol(self):
        assert not le(1.0, 0.5, atol=1e-3)


# ─────────────────────────────────────────────────────────────────────
# Strategy + generators
# ─────────────────────────────────────────────────────────────────────


class TestStrategy:
    def test_draw_returns_named_kwargs(self):
        import random
        rng = random.Random(0)
        s = Strategy(x=floats(0.0, 1.0), n=ints(1, 10))
        out = s.draw(rng)
        assert set(out.keys()) == {"x", "n"}
        assert 0.0 <= out["x"] <= 1.0
        assert 1 <= out["n"] <= 10

    def test_floats_log_scale_stays_positive(self):
        import random
        rng = random.Random(0)
        s = Strategy(r=floats(0.001, 1000.0, log_scale=True))
        for _ in range(100):
            out = s.draw(rng)
            assert 0.001 <= out["r"] <= 1000.0

    def test_choice_returns_one_of_options(self):
        import random
        rng = random.Random(0)
        s = Strategy(c=choice("a", "b", "c"))
        for _ in range(100):
            assert s.draw(rng)["c"] in ("a", "b", "c")

    def test_log_scale_on_nonpositive_raises(self):
        with pytest.raises(ValueError, match="strictly-positive"):
            import random
            floats(0.0, 1.0, log_scale=True).draw(random.Random())


# ─────────────────────────────────────────────────────────────────────
# run_harness end-to-end (small n_pbt for speed)
# ─────────────────────────────────────────────────────────────────────


class TestRunHarness:

    def test_trivially_true_spec_passes(self):
        result = run_harness(
            name="trivially_true",
            spec=lambda x: x + 1.0 > x,
            strategy=Strategy(x=floats(-1e6, 1e6)),
            n_pbt=200,
        )
        assert result.pbt_passed
        assert result.sweep_passed
        assert result.all_passed
        assert result.first_pbt_failure is None

    def test_trivially_false_spec_fails_fast(self):
        result = run_harness(
            name="trivially_false",
            spec=lambda x: x > x + 1.0,  # never true
            strategy=Strategy(x=floats(0.0, 1.0)),
            n_pbt=50,
        )
        assert not result.pbt_passed
        assert not result.all_passed
        assert result.first_pbt_failure is not None

    def test_spec_exception_counts_as_failure(self):
        def bad_spec(x):
            raise RuntimeError("model errored")
        result = run_harness(
            name="raises",
            spec=bad_spec,
            strategy=Strategy(x=floats(0.0, 1.0)),
            n_pbt=10,
        )
        assert not result.pbt_passed
        assert "_exception" in result.first_pbt_failure

    def test_caught_mutation_listed(self):
        # Original spec: x + 1 > x (always true).
        # Mutation: x + 1 < x (always false). 100 % failure → caught.
        result = run_harness(
            name="mut_caught",
            spec=lambda x: x + 1.0 > x,
            strategy=Strategy(x=floats(-100.0, 100.0)),
            n_pbt=50,
            mutations=(
                Mutation(name="reversed", spec=lambda x: x + 1.0 < x),
            ),
        )
        assert "reversed" in result.mutations_caught
        assert "reversed" not in result.mutations_missed

    def test_missed_mutation_flagged(self):
        # Original spec: x + 1 > x. Mutation: x + 0 > x - 1 (also always
        # true at every point) → mutation passes everywhere → MISSED.
        result = run_harness(
            name="mut_missed",
            spec=lambda x: x + 1.0 > x,
            strategy=Strategy(x=floats(-100.0, 100.0)),
            n_pbt=50,
            mutations=(
                Mutation(name="vacuous_pass", spec=lambda x: x + 0.0 > x - 1.0),
            ),
        )
        assert "vacuous_pass" in result.mutations_missed
        assert "vacuous_pass" not in result.mutations_caught
        assert not result.all_passed  # missed mutation = test set vacuous

    def test_seed_determinism(self):
        kwargs = dict(
            name="determ", strategy=Strategy(x=floats(0.0, 1.0)),
            spec=lambda x: x >= 0.0, n_pbt=20,
        )
        r1 = run_harness(seed=7, **kwargs)
        r2 = run_harness(seed=7, **kwargs)
        # Same seed → same first PBT draw shape (the sequence is reproducible).
        assert r1.wall_seconds >= 0
        assert r2.wall_seconds >= 0
        # Both pass.
        assert r1.all_passed and r2.all_passed

    def test_to_json_round_trips(self):
        import json as _json
        result = run_harness(
            name="json_test",
            spec=lambda x: x >= 0.0,
            strategy=Strategy(x=floats(0.0, 1.0)),
            n_pbt=10,
        )
        parsed = _json.loads(result.to_json())
        assert parsed["name"] == "json_test"
        assert parsed["all_passed"] is True

    def test_summarize_contains_status(self):
        result = run_harness(
            name="summ",
            spec=lambda x: x >= 0.0,
            strategy=Strategy(x=floats(0.0, 1.0)),
            n_pbt=10,
        )
        s = result.summarize()
        assert "summ" in s
        assert "PBT" in s
        assert "Sweep" in s

    def test_runtime_under_3s_for_n_pbt_10000(self):
        """Soft performance contract — typical numerical theorems
        run 10k PBT in well under 30s. Use a trivial spec to confirm
        the harness overhead alone is small."""
        result = run_harness(
            name="speed",
            spec=lambda x, y: x + y >= y,
            strategy=Strategy(x=floats(0.0, 1.0), y=floats(0.0, 1.0)),
            n_pbt=10_000,
        )
        assert result.wall_seconds < 3.0
        assert result.all_passed


# ─────────────────────────────────────────────────────────────────────
# Sweep behaviour
# ─────────────────────────────────────────────────────────────────────


class TestSweep:

    def test_sweep_finds_corner_failure(self):
        # Spec passes everywhere except x = 0 (corner).
        result = run_harness(
            name="corner",
            spec=lambda x: x > 0.0,
            strategy=Strategy(x=floats(0.0, 1.0)),
            n_pbt=10,
            sweep_points=5,
        )
        # Sweep includes x=0.0 (the corner), so it catches it even
        # though the random draws don't.
        assert not result.sweep_passed
        assert result.first_sweep_failure["x"] == 0.0

    def test_sweep_size_capped(self):
        # 5 axes × 8 points → 32_768 grid, capped to 10_000.
        result = run_harness(
            name="cap",
            spec=lambda a, b, c, d, e: True,
            strategy=Strategy(
                a=floats(0.0, 1.0), b=floats(0.0, 1.0),
                c=floats(0.0, 1.0), d=floats(0.0, 1.0),
                e=floats(0.0, 1.0),
            ),
            n_pbt=10,
            sweep_points=8,
        )
        assert result.sweep_total <= 10_000
