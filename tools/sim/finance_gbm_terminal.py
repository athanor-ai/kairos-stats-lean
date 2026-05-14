"""Geometric Brownian Motion closed-form terminal value: empirical companion.

Lean side (`Pythia/Finance/GeometricBrownianMotion.lean`):
  * `gbmTerminal S_0 μ σ T w := S_0 · exp((μ - σ²/2)·T + σ·w)`
  * `gbmTerminal_pos : 0 < S_0 → 0 < gbmTerminal`
  * `gbmTerminal_zero_time : at T=0, w=0 → S_0`
  * `log_gbmTerminal : log(gbmTerminal) = log S_0 + (μ - σ²/2)T + σw`

This module verifies the closed form numerically and confirms
non-vacuity through mutation harnesses.

Run:
    python3 -m tools.sim.finance_gbm_terminal

Or via pytest:
    pytest tools/sim/finance_gbm_terminal.py
"""
from __future__ import annotations

import math

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    run_harness,
)


def gbm_terminal(S_0: float, mu: float, sigma: float, T: float, w: float) -> float:
    return S_0 * math.exp((mu - sigma * sigma / 2) * T + sigma * w)


def gbm_terminal_pos_spec(S_0: float, mu: float, sigma: float, T: float, w: float) -> bool:
    if S_0 <= 0:
        return True  # premise fails; theorem holds vacuously
    return gbm_terminal(S_0, mu, sigma, T, w) > 0


def log_gbm_terminal_spec(S_0: float, mu: float, sigma: float, T: float, w: float) -> bool:
    """log(GBM) = log S_0 + (μ - σ²/2)·T + σ·w."""
    if S_0 <= 0:
        return True
    lhs = math.log(gbm_terminal(S_0, mu, sigma, T, w))
    rhs = math.log(S_0) + (mu - sigma * sigma / 2) * T + sigma * w
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Mutations
# ============================================================================


def _drop_ito_correction(S_0: float, mu: float, sigma: float, T: float, w: float) -> bool:
    """Drops the Itô -σ²/2 correction term. Fails when σ²T is nonzero."""
    if S_0 <= 0:
        return True
    mutant = S_0 * math.exp(mu * T + sigma * w)
    lhs = math.log(mutant) if mutant > 0 else float("inf")
    rhs = math.log(S_0) + (mu - sigma * sigma / 2) * T + sigma * w
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _wrong_ito_sign(S_0: float, mu: float, sigma: float, T: float, w: float) -> bool:
    """Wrong-sign on the Itô correction: +σ²/2 instead of -σ²/2.
    Fails when σ²T nonzero."""
    if S_0 <= 0:
        return True
    mutant = S_0 * math.exp((mu + sigma * sigma / 2) * T + sigma * w)
    lhs = math.log(mutant) if mutant > 0 else float("inf")
    rhs = math.log(S_0) + (mu - sigma * sigma / 2) * T + sigma * w
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _missing_brownian_term(S_0: float, mu: float, sigma: float, T: float, w: float) -> bool:
    """Drops the σ·w Brownian-sample term. Fails when σ·w nonzero."""
    if S_0 <= 0:
        return True
    mutant = S_0 * math.exp((mu - sigma * sigma / 2) * T)
    lhs = math.log(mutant) if mutant > 0 else float("inf")
    rhs = math.log(S_0) + (mu - sigma * sigma / 2) * T + sigma * w
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


def _additive_not_multiplicative(S_0: float, mu: float, sigma: float, T: float, w: float) -> bool:
    """Additive form S_0 + exp(...) instead of S_0 · exp(...).
    Breaks the log relation entirely."""
    if S_0 <= 0:
        return True
    mutant = S_0 + math.exp((mu - sigma * sigma / 2) * T + sigma * w)
    lhs = math.log(mutant) if mutant > 0 else float("inf")
    rhs = math.log(S_0) + (mu - sigma * sigma / 2) * T + sigma * w
    return math.isclose(lhs, rhs, abs_tol=1e-9, rel_tol=1e-9)


# ============================================================================
# Strategies
# ============================================================================


_strategy = Strategy(
    S_0=floats(lo=0.01, hi=1e4, log_scale=True),
    mu=floats(lo=-0.5, hi=0.5),
    sigma=floats(lo=0.01, hi=2.0),
    T=floats(lo=0.01, hi=10.0),
    w=floats(lo=-4.0, hi=4.0),
)


# ============================================================================
# Tests
# ============================================================================


def test_gbm_terminal_pos():
    # Positivity-only test has no useful single-spec mutations
    # (any positive function passes); the log_gbm_terminal test below
    # carries the mutation-catching weight.
    result = run_harness(
        name="gbm_terminal_pos",
        spec=gbm_terminal_pos_spec,
        strategy=_strategy,
    )
    assert result.all_passed, result.summarize()


def test_log_gbm_terminal():
    result = run_harness(
        name="log_gbm_terminal",
        spec=log_gbm_terminal_spec,
        strategy=_strategy,
        mutations=(
            Mutation("drop_ito_correction", _drop_ito_correction, min_failure_rate=0.50),
            Mutation("wrong_ito_sign", _wrong_ito_sign, min_failure_rate=0.50),
            Mutation("missing_brownian_term", _missing_brownian_term, min_failure_rate=0.30),
            Mutation("additive_not_multiplicative", _additive_not_multiplicative, min_failure_rate=0.50),
        ),
    )
    assert result.all_passed, result.summarize()


if __name__ == "__main__":
    test_gbm_terminal_pos()
    test_log_gbm_terminal()
    print("gbm_terminal: PBT + mutation tests passed.")
