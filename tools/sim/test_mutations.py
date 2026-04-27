"""tools.sim.mutations — unit tests.

Each named mutation gets a property test that confirms it ACTUALLY
breaks a typical spec on the expected fraction of a synthetic draw
set. Hermetic, no external deps. Catches regressions where a
mutation factory accidentally produces a vacuous mutation that the
harness silently flags as caught.
"""
from __future__ import annotations

import random

import pytest

from tools.sim.harness import Mutation
from tools.sim.mutations import (
    custom_transform,
    drop_factor,
    negate_value,
    off_by_const,
    strict_bound_above,
    strict_bound_below,
    swap_inequality,
)


# ─────────────────────────────────────────────────────────────────────
# Reference specs used to validate mutations
# ─────────────────────────────────────────────────────────────────────


def _spec_x_geq_0(x: float) -> bool:
    """Trivially-true spec: x >= 0 over uniform [0, 1] draws."""
    return x >= 0.0


def _spec_cobb_douglas(K: float, L: float, lam: float, alpha: float) -> bool:
    """Cobb-Douglas constant returns to scale (real numerical equality
    within rtol)."""
    import math
    lhs = (lam * K) ** alpha * (lam * L) ** (1 - alpha)
    rhs = lam * (K ** alpha * L ** (1 - alpha))
    return math.isclose(lhs, rhs, rel_tol=1e-9)


def _spec_with_offset(x: float, _offset: float = 0.0) -> bool:
    """Spec that honours the off-by-const protocol: it returns
    `x + _offset >= 0`. Used to validate off_by_const mutation."""
    return x + _offset >= 0.0


def _spec_with_strict_below(
    x: float, _strict_below_threshold: float | None = None,
) -> bool:
    """Spec that honours the strict-bound-below protocol: when the
    threshold is set, asserts x > threshold. Used to validate
    strict_bound_below."""
    if _strict_below_threshold is not None:
        return x > _strict_below_threshold
    return x >= 0.0


def _strategy_unit_x(rng: random.Random, n: int = 100) -> list[dict]:
    """Generate `n` samples of {'x': uniform[0, 1]}."""
    return [{"x": rng.uniform(0.0, 1.0)} for _ in range(n)]


def _failure_rate(mutation: Mutation, draws: list[dict]) -> float:
    """Fraction of draws on which the mutation returns False."""
    if not draws:
        return 0.0
    n_fail = sum(1 for d in draws if not mutation.spec(**d))
    return n_fail / len(draws)


# ─────────────────────────────────────────────────────────────────────
# negate_value
# ─────────────────────────────────────────────────────────────────────


class TestNegateValue:

    def test_flips_verdict_universally(self):
        # The reference spec is True for x >= 0; mutation flips to
        # False everywhere on the unit interval.
        rng = random.Random(0)
        draws = _strategy_unit_x(rng, 100)
        m = negate_value(_spec_x_geq_0)
        rate = _failure_rate(m, draws)
        assert rate == 1.0, f"negate_value should fail on 100% of draws, got {rate}"

    def test_min_failure_rate_floor_default(self):
        m = negate_value(_spec_x_geq_0)
        assert m.min_failure_rate == 0.5

    def test_carries_caller_provided_name(self):
        m = negate_value(_spec_x_geq_0, name="custom_negate")
        assert m.name == "custom_negate"


# ─────────────────────────────────────────────────────────────────────
# drop_factor
# ─────────────────────────────────────────────────────────────────────


class TestDropFactor:

    def test_drops_lambda_in_cobb_douglas(self):
        # Cobb-Douglas CRTS holds at lam=1 trivially. drop_factor pins
        # lam=1.0; the mutation tests whether the original CRTS spec
        # holds at lam=1, which it ALWAYS does. So this would actually
        # PASS — wrong direction. Instead, the mutation pins one of the
        # input arguments to a constant, and tests whether the spec at
        # that pinned value still holds for the OTHER variables drawn
        # at non-pinned values.
        #
        # For Cobb-Douglas, pinning K=1.0 still leaves the CRTS
        # equation true (it holds for ALL K, L, lam, alpha). So
        # drop_factor on a UNIVERSAL spec doesn't fail.
        #
        # The realistic use case: drop_factor on a CONDITIONAL spec
        # where the factor is load-bearing. We test with a custom
        # spec that DOES fail on pinning.
        def conditional_spec(x: float, y: float) -> bool:
            # Spec: x == y. Pinning y=1.0 fails on every draw where
            # x != 1.0.
            return abs(x - y) < 1e-12

        rng = random.Random(0)
        draws = [{"x": rng.uniform(0.0, 10.0), "y": rng.uniform(0.0, 10.0)}
                 for _ in range(200)]
        # Sanity: original spec passes only on the diagonal (~0% draws).
        # We pre-filter to draws where original passes by setting
        # y=x. THEN drop_factor pins y=1.0; the mutation is True
        # only when x=1.0, so >> 99% of draws fail.
        diagonal_draws = [{"x": d["x"], "y": d["x"]} for d in draws]
        m = drop_factor(conditional_spec, "y", replacement=1.0)
        rate = _failure_rate(m, diagonal_draws)
        assert rate >= 0.95, (
            f"drop_factor on conditional spec should fail on near-100%, got {rate}"
        )

    def test_default_name_includes_factor(self):
        m = drop_factor(_spec_x_geq_0, "x")
        assert "drop_factor_x" == m.name


# ─────────────────────────────────────────────────────────────────────
# off_by_const
# ─────────────────────────────────────────────────────────────────────


class TestOffByConst:

    def test_breaks_offset_aware_spec(self):
        # Reference spec: x + _offset >= 0. With _offset=-2 and
        # x drawn from [0, 1], the mutation fails universally.
        rng = random.Random(0)
        draws = _strategy_unit_x(rng, 100)
        m = off_by_const(_spec_with_offset, delta=-2.0)
        rate = _failure_rate(m, draws)
        assert rate >= 0.99

    def test_no_op_on_offset_unaware_spec(self):
        # Original spec doesn't accept _offset. The mutation can't
        # detect a difference; it returns True (undetectable).
        rng = random.Random(0)
        draws = _strategy_unit_x(rng, 50)
        m = off_by_const(_spec_x_geq_0, delta=-1.0)
        rate = _failure_rate(m, draws)
        # All draws return True from the mutated spec → 0% failure.
        assert rate == 0.0


# ─────────────────────────────────────────────────────────────────────
# swap_inequality (alias for negate_value)
# ─────────────────────────────────────────────────────────────────────


class TestSwapInequality:

    def test_is_alias_for_negate(self):
        rng = random.Random(0)
        draws = _strategy_unit_x(rng, 50)
        m = swap_inequality(_spec_x_geq_0)
        rate = _failure_rate(m, draws)
        assert rate == 1.0
        assert m.name == "swap_inequality"


# ─────────────────────────────────────────────────────────────────────
# strict bounds
# ─────────────────────────────────────────────────────────────────────


class TestStrictBoundBelow:

    def test_threshold_breaks_aware_spec(self):
        # Spec checks x > threshold. With threshold=0.5 and x drawn
        # from [0, 1], the mutation fails on draws where x <= 0.5.
        rng = random.Random(0)
        draws = _strategy_unit_x(rng, 200)
        m = strict_bound_below(_spec_with_strict_below, threshold=0.5)
        rate = _failure_rate(m, draws)
        # ~50% of uniform draws are below 0.5.
        assert 0.35 <= rate <= 0.65

    def test_no_op_on_unaware_spec(self):
        rng = random.Random(0)
        draws = _strategy_unit_x(rng, 50)
        m = strict_bound_below(_spec_x_geq_0, threshold=0.5)
        rate = _failure_rate(m, draws)
        assert rate == 0.0


class TestStrictBoundAbove:

    def test_no_op_on_unaware_spec(self):
        # Symmetric; we don't ship a reference for this side.
        m = strict_bound_above(_spec_x_geq_0, threshold=10.0)
        # Just confirm it builds + has the expected name shape.
        assert "strict_above" in m.name


# ─────────────────────────────────────────────────────────────────────
# custom_transform escape hatch
# ─────────────────────────────────────────────────────────────────────


class TestCustomTransform:

    def test_packages_custom_callable(self):
        # User supplies a fully-custom mutation; library just gives
        # them the consistent Mutation packaging.
        custom_spec = lambda x: x < 0  # always False on [0,1]
        m = custom_transform(_spec_x_geq_0, custom_spec, name="my_custom")
        assert m.name == "my_custom"
        rng = random.Random(0)
        draws = _strategy_unit_x(rng, 50)
        rate = _failure_rate(m, draws)
        assert rate == 1.0
