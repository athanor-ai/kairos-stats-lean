"""Unit tests for tools.sim.harness.v2.metamorphic."""
from __future__ import annotations

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from tools.sim.harness.v2.generators import real_in, bounded_iid
from tools.sim.harness.v2.metamorphic import (
    MetamorphicRelation,
    bilinear,
    homogeneous,
    limit_case,
    permutation_invariant,
    subadditive,
    time_reversal_invariant,
)


def _scalar_strategy():
    return st.fixed_dictionaries({"x": real_in(0.1, 10.0)})


def _two_scalar_strategy():
    return st.fixed_dictionaries({"x": real_in(0.1, 10.0), "y": real_in(0.1, 10.0)})


class TestMetamorphicRelation:
    def test_is_dataclass(self) -> None:
        mr = MetamorphicRelation(name="test", check=lambda: None)
        assert mr.name == "test"

    def test_run_calls_check(self) -> None:
        called = []
        mr = MetamorphicRelation(name="t", check=lambda: called.append(1))
        mr.run()
        assert called == [1]


class TestHomogeneous:
    def test_linear_fn_is_homogeneous(self) -> None:
        # f(x) = 3x is homogeneous of degree 1
        mr = homogeneous(
            fn=lambda x: 3 * x,
            arg_names=["x"],
            factor_strategy=real_in(0.1, 5.0),
            exponent=1,
            base_strategy=_scalar_strategy(),
            max_examples=50,
        )
        assert mr.name == "homogeneous(k=1)"
        mr.run()  # should not raise

    def test_quadratic_is_degree_2(self) -> None:
        mr = homogeneous(
            fn=lambda x: x ** 2,
            arg_names=["x"],
            factor_strategy=real_in(0.5, 3.0),
            exponent=2,
            base_strategy=_scalar_strategy(),
            max_examples=50,
        )
        mr.run()

    def test_wrong_exponent_raises(self) -> None:
        mr = homogeneous(
            fn=lambda x: x ** 2,
            arg_names=["x"],
            factor_strategy=real_in(1.5, 3.0),
            exponent=1,  # wrong
            base_strategy=_scalar_strategy(),
            max_examples=10,
        )
        with pytest.raises(Exception):
            mr.run()


class TestPermutationInvariant:
    def test_sum_is_invariant(self) -> None:
        mr = permutation_invariant(
            fn=lambda x, y: x + y,
            arg_names=["x", "y"],
            base_strategy=_two_scalar_strategy(),
            max_examples=50,
        )
        mr.run()

    def test_max_is_invariant(self) -> None:
        mr = permutation_invariant(
            fn=lambda x, y: max(x, y),
            arg_names=["x", "y"],
            base_strategy=_two_scalar_strategy(),
            max_examples=50,
        )
        mr.run()


class TestTimeReversalInvariant:
    def test_sum_of_squares_is_invariant(self) -> None:
        mr = time_reversal_invariant(
            fn=lambda path: sum(x ** 2 for x in path),
            path_strategy=bounded_iid(-5.0, 5.0, 5),
            max_examples=50,
        )
        mr.run()


class TestBilinear:
    def test_product_is_bilinear(self) -> None:
        mr = bilinear(
            fn=lambda x, y: x * y,
            arg1="x",
            arg2="y",
            base_strategy=_two_scalar_strategy(),
            scalar_strategy=real_in(0.5, 3.0),
            max_examples=50,
        )
        mr.run()


class TestSubadditive:
    def test_sqrt_is_subadditive_on_nonneg(self) -> None:
        import math
        base = st.fixed_dictionaries({"x": real_in(0.0, 100.0)})
        mr = subadditive(
            fn=lambda x: math.sqrt(x),
            arg_names=["x"],
            base_strategy=base,
            max_examples=50,
        )
        mr.run()


class TestLimitCase:
    def test_limit_at_zero_returns_constant(self) -> None:
        # f(x, offset) at offset=0 should equal f(x, 0)=x
        mr = limit_case(
            fn=lambda x, offset: x + offset,
            arg="offset",
            limit_value=0.0,
            expected_form_fn=lambda x, offset: x,
            base_strategy=st.fixed_dictionaries({
                "x": real_in(0.1, 10.0),
                "offset": real_in(-5.0, 5.0),
            }),
            max_examples=50,
        )
        mr.run()
