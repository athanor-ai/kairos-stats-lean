"""Unit tests for tools.sim.harness.v2.statistical."""
from __future__ import annotations

import pytest

from tools.sim.harness.v2.statistical import (
    binomial_ci_check,
    clopper_pearson_ci,
    wilson_ci,
)


class TestWilsonCi:
    def test_zero_n(self) -> None:
        lo, hi = wilson_ci(0, 0)
        assert lo == 0.0 and hi == 1.0

    def test_zero_successes_lower_is_zero(self) -> None:
        lo, hi = wilson_ci(0, 100)
        assert lo == 0.0
        assert hi > 0.0  # upper bound is positive (uncertainty about rare event)

    def test_zero_successes_upper_below_15pct(self) -> None:
        # 99% CI for 0/100 should have upper well below 15%
        lo, hi = wilson_ci(0, 100, level=0.99)
        assert hi < 0.15

    def test_all_successes_upper_is_one(self) -> None:
        lo, hi = wilson_ci(100, 100)
        assert hi == 1.0

    def test_all_successes_lower_above_90pct(self) -> None:
        lo, hi = wilson_ci(100, 100, level=0.99)
        assert lo > 0.90

    def test_half_successes(self) -> None:
        lo, hi = wilson_ci(50, 100, level=0.99)
        assert lo < 0.5 < hi

    def test_bounds_in_01(self) -> None:
        lo, hi = wilson_ci(7, 100, level=0.95)
        assert 0.0 <= lo <= hi <= 1.0

    def test_returns_floats(self) -> None:
        lo, hi = wilson_ci(5, 100)
        # Accept numpy floats or Python floats
        assert float(lo) >= 0.0
        assert float(hi) <= 1.0


class TestClopperPearsonCi:
    def test_zero_n(self) -> None:
        lo, hi = clopper_pearson_ci(0, 0)
        assert lo == 0.0 and hi == 1.0

    def test_zero_successes_lower_is_zero(self) -> None:
        lo, hi = clopper_pearson_ci(0, 100)
        assert lo == 0.0
        assert hi > 0.0

    def test_zero_successes_upper_below_15pct(self) -> None:
        lo, hi = clopper_pearson_ci(0, 100, level=0.99)
        assert hi < 0.15

    def test_all_successes_upper_is_one(self) -> None:
        lo, hi = clopper_pearson_ci(100, 100)
        assert hi == 1.0

    def test_all_successes_lower_above_90pct(self) -> None:
        lo, hi = clopper_pearson_ci(100, 100, level=0.99)
        assert lo > 0.90

    def test_bounds_ordered(self) -> None:
        lo, hi = clopper_pearson_ci(20, 200)
        assert float(lo) <= float(hi)

    def test_interval_contains_mle(self) -> None:
        # MLE is k/n = 5/100 = 0.05; CI should straddle it
        lo, hi = clopper_pearson_ci(5, 100, level=0.99)
        assert float(lo) < 0.05 < float(hi)


class TestBinomialCiCheck:
    def test_zero_violations_many_trials_passes(self) -> None:
        # 0/1000 violations; upper CI for 99% level is ~0.003, well under 5%
        assert binomial_ci_check(0, 1000, claimed_prob=0.05)

    def test_many_violations_fails(self) -> None:
        # 200/1000 = 20% violation rate; upper CI far exceeds 5%
        assert not binomial_ci_check(200, 1000, claimed_prob=0.05)

    def test_high_claimed_prob_passes(self) -> None:
        # 10/100 violations; upper CI at 99% is ~20.2%; claim=0.25 should pass
        assert binomial_ci_check(10, 100, claimed_prob=0.25)

    def test_low_claimed_prob_fails(self) -> None:
        # 10/100 violations; upper CI at 99% is ~18%; claim=0.05 must fail
        assert not binomial_ci_check(10, 100, claimed_prob=0.05)

    def test_wilson_method_high_n(self) -> None:
        # 0/1000 with Wilson; upper CI very small
        assert binomial_ci_check(0, 1000, claimed_prob=0.05, method="wilson")

    def test_clopper_pearson_method_high_n(self) -> None:
        assert binomial_ci_check(0, 1000, claimed_prob=0.05, method="clopper_pearson")

    def test_result_is_bool_compatible(self) -> None:
        result = binomial_ci_check(0, 1000, claimed_prob=0.05)
        # Should be truthy/falsy regardless of numpy vs Python bool
        assert bool(result) is True
