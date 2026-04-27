"""Unit tests for tools.sim.harness.v2.properties."""
from __future__ import annotations

import math

import pytest

from tools.sim.harness.v2.properties import (
    convergence,
    ergodic_match,
    identity,
    martingale_property,
    monotone,
    tail_bound,
)


class TestTailBound:
    def test_empty_samples(self) -> None:
        assert tail_bound([], 0.5, 0.1) is True

    def test_no_violations(self) -> None:
        samples = [0.1, 0.2, 0.3]
        assert tail_bound(samples, threshold=0.5, claimed_bound=0.0) is True

    def test_all_violations(self) -> None:
        samples = [1.0, 2.0, 3.0]
        assert tail_bound(samples, threshold=0.5, claimed_bound=0.5) is False

    def test_boundary_pass(self) -> None:
        # Exactly 10% violations, claim <= 10%
        samples = [0.0] * 9 + [1.0]
        assert tail_bound(samples, threshold=0.5, claimed_bound=0.1) is True

    def test_atol_slack(self) -> None:
        samples = [1.0] * 2 + [0.0] * 8  # 20% violations
        # Without atol: 0.2 > 0.1 → fail
        assert tail_bound(samples, threshold=0.5, claimed_bound=0.1) is False
        # With atol: 0.2 <= 0.1 + 0.15 → pass
        assert tail_bound(samples, threshold=0.5, claimed_bound=0.1, atol=0.15) is True


class TestIdentity:
    def test_equal_functions(self) -> None:
        assert identity(lambda x: x + 0, lambda x: x, {"x": 5.0}) is True

    def test_near_equal(self) -> None:
        assert identity(lambda x: x * 1.0, lambda x: x, {"x": 1e10}, tolerance=1e-9) is True

    def test_different_functions(self) -> None:
        assert identity(lambda x: x + 1, lambda x: x, {"x": 5.0}) is False

    def test_symbolic_flag_accepted(self) -> None:
        # symbolic=True must not raise, falls back to numeric
        assert identity(lambda x: x, lambda x: x, {"x": 3.14}, symbolic=True) is True


class TestMonotone:
    def test_increasing_fn(self) -> None:
        assert monotone(lambda x: x ** 2, {"x": 1.0}, "x", lo=0.0, hi=10.0) is True

    def test_decreasing_fn_fails(self) -> None:
        assert monotone(lambda x: -x, {"x": 1.0}, "x", lo=0.0, hi=5.0) is False

    def test_constant_fn(self) -> None:
        assert monotone(lambda x: 3.0, {"x": 1.0}, "x", lo=0.0, hi=5.0) is True


class TestConvergence:
    def test_converges_to_zero(self) -> None:
        assert convergence(lambda t: 1.0 / t, target=0.0, n_steps=100_000) is True

    def test_never_converges(self) -> None:
        assert convergence(lambda t: math.sin(t), target=0.0, n_steps=1000) is False

    def test_single_step(self) -> None:
        assert convergence(lambda t: 0.0, target=0.0, n_steps=1) is True


class TestMartingaleProperty:
    def test_constant_path(self) -> None:
        assert martingale_property([1.0, 1.0, 1.0]) is True

    def test_single_element(self) -> None:
        assert martingale_property([42.0]) is True

    def test_non_martingale(self) -> None:
        path = [0.0, 1.0, 2.0]
        assert martingale_property(path) is False

    def test_with_filtration(self) -> None:
        path = [2.0, 2.0, 2.0]
        filtration = lambda p, t: p[t]
        assert martingale_property(path, filtration) is True

    def test_non_martingale_with_filtration(self) -> None:
        path = [1.0, 2.0, 4.0]
        filtration = lambda p, t: p[t]
        assert martingale_property(path, filtration) is False


class TestErgodicMatch:
    def test_exact_match(self) -> None:
        assert ergodic_match(0.5, 0.5) is True

    def test_within_tolerance(self) -> None:
        assert ergodic_match(0.5, 0.5009, tolerance=0.001) is True

    def test_outside_tolerance(self) -> None:
        assert ergodic_match(0.0, 1.0, tolerance=0.001) is False
