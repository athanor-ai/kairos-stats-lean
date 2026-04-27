"""Unit tests for tools.sim.harness.v2.targeting."""
from __future__ import annotations

import pytest
from hypothesis.strategies import SearchStrategy

from tools.sim.harness.v2.generators import real_in
from tools.sim.harness.v2.targeting import (
    target_extreme,
    target_violation_proximity,
)


class TestTargetExtreme:
    def test_returns_strategy(self) -> None:
        s = target_extreme(real_in(-10, 10), lambda v: abs(v))
        assert isinstance(s, SearchStrategy)

    def test_annotates_edge_fn(self) -> None:
        edge_fn = lambda v: abs(v)
        s = target_extreme(real_in(-10, 10), edge_fn)
        assert hasattr(s, "_v2_edge_fn")
        assert s._v2_edge_fn is edge_fn

    def test_strategy_still_draws(self) -> None:
        from hypothesis import given, settings
        s = target_extreme(real_in(0.0, 1.0), lambda v: v)

        @settings(max_examples=20)
        @given(x=s)
        def inner(x: float) -> None:
            assert 0.0 <= x <= 1.0

        inner()


class TestTargetViolationProximity:
    def test_returns_strategy(self) -> None:
        import hypothesis.strategies as st
        base = st.fixed_dictionaries({"x": real_in(0.0, 10.0)})
        s = target_violation_proximity(lambda x: x, base)
        assert isinstance(s, SearchStrategy)

    def test_annotates_bound_fn(self) -> None:
        import hypothesis.strategies as st
        base = st.fixed_dictionaries({"x": real_in(0.0, 10.0)})
        bound_fn = lambda x: x
        s = target_violation_proximity(bound_fn, base)
        assert hasattr(s, "_v2_bound_fn")
        assert s._v2_bound_fn is bound_fn

    def test_strategy_still_draws(self) -> None:
        from hypothesis import given, settings
        import hypothesis.strategies as st
        base = st.fixed_dictionaries({"x": real_in(0.0, 1.0)})
        s = target_violation_proximity(lambda x: 1.0 - x, base)

        @settings(max_examples=20)
        @given(inputs=s)
        def inner(inputs: dict) -> None:
            assert 0.0 <= inputs["x"] <= 1.0

        inner()
