"""Unit tests for tools.sim.harness.v2.generators."""
from __future__ import annotations

import math

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from tools.sim.harness.v2.generators import (
    bounded_iid,
    bounded_real,
    positive_real,
    production_inputs,
    random_density,
    random_ode_initial,
    random_stochastic_matrix,
    real_in,
    sample_path_supermartingale,
    sub_gamma_sample,
    sub_gaussian_sample,
)


class TestPositiveReal:
    @given(x=positive_real())
    def test_strictly_positive(self, x: float) -> None:
        assert x > 0

    @given(x=positive_real())
    def test_finite(self, x: float) -> None:
        assert math.isfinite(x)


class TestRealIn:
    @given(x=real_in(-5.0, 5.0))
    def test_in_range(self, x: float) -> None:
        assert -5.0 <= x <= 5.0

    @given(x=real_in(0.0, 1.0))
    def test_unit_interval(self, x: float) -> None:
        assert 0.0 <= x <= 1.0

    def test_bounded_real_alias(self) -> None:
        # bounded_real and real_in should produce equivalent strategies
        import hypothesis
        s1 = real_in(0.0, 1.0)
        s2 = bounded_real(0.0, 1.0)
        # Both should be SearchStrategy instances
        from hypothesis.strategies import SearchStrategy
        assert isinstance(s1, SearchStrategy)
        assert isinstance(s2, SearchStrategy)


class TestBoundedIid:
    @given(samples=bounded_iid(0.0, 1.0, 10))
    def test_length(self, samples: list) -> None:
        assert len(samples) == 10

    @given(samples=bounded_iid(-1.0, 1.0, 5))
    def test_all_in_range(self, samples: list) -> None:
        assert all(-1.0 <= x <= 1.0 for x in samples)


class TestSubGaussianSample:
    @given(samples=sub_gaussian_sample(sigma=1.0, n=20))
    def test_length(self, samples: list) -> None:
        assert len(samples) == 20

    @given(samples=sub_gaussian_sample(sigma=2.0, n=50))
    def test_finite_values(self, samples: list) -> None:
        assert all(math.isfinite(x) for x in samples)


class TestSubGammaSample:
    @given(samples=sub_gamma_sample(variance=1.0, scale=0.5, n=10))
    def test_length(self, samples: list) -> None:
        assert len(samples) == 10

    @given(samples=sub_gamma_sample(variance=1.0, scale=0.5, n=10))
    def test_nonnegative(self, samples: list) -> None:
        assert all(x >= 0.0 for x in samples)


class TestSamplePathSupermartingale:
    @given(path=sample_path_supermartingale(steps=10, drift_max=0.5))
    def test_length(self, path: list) -> None:
        assert len(path) == 11  # steps + 1 (includes X_0=0)

    @given(path=sample_path_supermartingale(steps=5, drift_max=0.1))
    def test_starts_at_zero(self, path: list) -> None:
        assert path[0] == 0.0

    @given(path=sample_path_supermartingale(steps=20, drift_max=1.0))
    def test_non_increasing_trend(self, path: list) -> None:
        # Path should generally be non-increasing (increments <= 0)
        # Allow floating point slack but verify final <= start
        assert path[-1] <= path[0] + 1e-10


class TestRandomOdeInitial:
    @given(state=random_ode_initial(state_dim=3))
    def test_length(self, state: list) -> None:
        assert len(state) == 3

    @given(state=random_ode_initial(state_dim=5))
    def test_bounded(self, state: list) -> None:
        assert all(-10.0 <= x <= 10.0 for x in state)


class TestRandomDensity:
    @given(p=random_density(simplex_dim=4))
    def test_length(self, p: list) -> None:
        assert len(p) == 4

    @given(p=random_density(simplex_dim=3))
    def test_sums_to_one(self, p: list) -> None:
        assert abs(sum(p) - 1.0) < 1e-10

    @given(p=random_density(simplex_dim=5))
    def test_nonnegative(self, p: list) -> None:
        assert all(x >= 0.0 for x in p)


class TestRandomStochasticMatrix:
    @given(M=random_stochastic_matrix(d=3))
    def test_shape(self, M: list) -> None:
        assert len(M) == 3
        assert all(len(row) == 3 for row in M)

    @given(M=random_stochastic_matrix(d=2))
    def test_rows_sum_to_one(self, M: list) -> None:
        for row in M:
            assert abs(sum(row) - 1.0) < 1e-10


class TestProductionInputs:
    @given(inputs=production_inputs(alpha=0.3, K=1000.0, L=500.0))
    def test_keys(self, inputs: dict) -> None:
        assert set(inputs.keys()) == {"K", "L", "alpha"}

    @given(inputs=production_inputs(alpha=0.5, K=100.0, L=200.0))
    def test_alpha_fixed(self, inputs: dict) -> None:
        assert inputs["alpha"] == 0.5

    @given(inputs=production_inputs(alpha=0.3, K=1000.0, L=500.0))
    def test_K_in_range(self, inputs: dict) -> None:
        assert 1e-2 <= inputs["K"] <= 1000.0
