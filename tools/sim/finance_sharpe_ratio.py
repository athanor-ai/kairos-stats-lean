"""Sharpe ratio (algebraic form): empirical companion.

Lean side (`Pythia/Finance/SharpeRatio.lean` + `SharpeBridge.lean`):
  * `sharpeRatio μ rf σ := (μ - rf) / σ`
  * `sharpeRatio_pos` / `sharpeRatio_mono_excess` / `sharpeRatio_scale_invariant`
  * `sharpe_diff_eq_excess_over_sigma` : structural Lipschitz identity
  * `sharpe_cs_band` : mean-CS band B translates to Sharpe-CS band B/σ

Run:
    python3 -m tools.sim.finance_sharpe_ratio

Or via pytest:
    pytest tools/sim/finance_sharpe_ratio.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def sharpe_ratio(mu: float, rf: float, sigma: float) -> float:
    return (mu - rf) / sigma


def sharpe_pos_spec(mu: float, rf: float, sigma: float) -> bool:
    if sigma <= 0 or not (rf < mu):
        return True  # premise fails
    return sharpe_ratio(mu, rf, sigma) > 0


def sharpe_diff_spec(mu_hat: float, mu_star: float, rf: float, sigma: float) -> bool:
    """Sharpe(μ̂) - Sharpe(μ*) = (μ̂ - μ*) / σ."""
    if sigma == 0:
        return True
    lhs = sharpe_ratio(mu_hat, rf, sigma) - sharpe_ratio(mu_star, rf, sigma)
    rhs = (mu_hat - mu_star) / sigma
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def sharpe_scale_invariant_spec(alpha: float, mu: float, rf: float, sigma: float) -> bool:
    """Sharpe(αμ, α·rf, α·σ) = Sharpe(μ, rf, σ) for α > 0."""
    if alpha <= 0 or sigma == 0:
        return True
    lhs = sharpe_ratio(alpha * mu, alpha * rf, alpha * sigma)
    rhs = sharpe_ratio(mu, rf, sigma)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Mutations
# ============================================================================


def _diff_drop_sigma(mu_hat: float, mu_star: float, rf: float, sigma: float) -> bool:
    """Drops the σ denominator on RHS. Fails when σ ≠ 1."""
    if sigma == 0:
        return True
    lhs = sharpe_ratio(mu_hat, rf, sigma) - sharpe_ratio(mu_star, rf, sigma)
    rhs = mu_hat - mu_star  # missing /sigma
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _diff_wrong_sign(mu_hat: float, mu_star: float, rf: float, sigma: float) -> bool:
    """Sharpe(μ̂) + Sharpe(μ*) instead of difference. Fails universally."""
    if sigma == 0:
        return True
    lhs = sharpe_ratio(mu_hat, rf, sigma) + sharpe_ratio(mu_star, rf, sigma)
    rhs = (mu_hat - mu_star) / sigma
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _scale_only_numerator(alpha: float, mu: float, rf: float, sigma: float) -> bool:
    """Scales only numerator args, not σ. Fails when α ≠ 1."""
    if alpha <= 0 or sigma == 0:
        return True
    lhs = sharpe_ratio(alpha * mu, alpha * rf, sigma)  # σ not scaled
    rhs = sharpe_ratio(mu, rf, sigma)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _scale_inverse(alpha: float, mu: float, rf: float, sigma: float) -> bool:
    """Scales σ by 1/α instead of α. Fails when α² ≠ 1."""
    if alpha <= 0 or sigma == 0:
        return True
    lhs = sharpe_ratio(alpha * mu, alpha * rf, sigma / alpha)
    rhs = sharpe_ratio(mu, rf, sigma)
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Strategies
# ============================================================================


_strategy_diff = Strategy(
    mu_hat=floats(lo=-1.0, hi=1.0),
    mu_star=floats(lo=-1.0, hi=1.0),
    rf=floats(lo=-0.1, hi=0.2),
    sigma=floats(lo=0.01, hi=2.0),
)


_strategy_scale = Strategy(
    alpha=floats(lo=0.1, hi=10.0, log_scale=True),
    mu=floats(lo=-1.0, hi=1.0),
    rf=floats(lo=-0.1, hi=0.2),
    sigma=floats(lo=0.01, hi=2.0),
)


_strategy_pos = Strategy(
    mu=floats(lo=-1.0, hi=1.0),
    rf=floats(lo=-0.1, hi=0.2),
    sigma=floats(lo=0.01, hi=2.0),
)


# ============================================================================
# Tests
# ============================================================================


def test_sharpe_pos():
    result = run_harness(
        name="sharpe_pos",
        spec=sharpe_pos_spec,
        strategy=_strategy_pos,
    )
    assert result.all_passed, result.summarize()


def test_sharpe_diff():
    result = run_harness(
        name="sharpe_diff_eq_excess_over_sigma",
        spec=sharpe_diff_spec,
        strategy=_strategy_diff,
        mutations=(
            Mutation("diff_drop_sigma", _diff_drop_sigma, min_failure_rate=0.50),
            Mutation("diff_wrong_sign", _diff_wrong_sign, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


def test_sharpe_scale_invariant():
    result = run_harness(
        name="sharpe_scale_invariant",
        spec=sharpe_scale_invariant_spec,
        strategy=_strategy_scale,
        mutations=(
            Mutation("scale_only_numerator", _scale_only_numerator, min_failure_rate=0.50),
            Mutation("scale_inverse", _scale_inverse, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


if __name__ == "__main__":
    test_sharpe_pos()
    test_sharpe_diff()
    test_sharpe_scale_invariant()
    print("sharpe_ratio: PBT + 4 mutation tests passed.")
