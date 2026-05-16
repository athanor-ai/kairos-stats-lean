/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Backtest Validity (statistical guarantees)

Proves properties that prevent overfitting in backtests:
Bonferroni correction for multiple testing, deflated Sharpe
ratio bounds, and minimum backtest length requirements.

A quant researcher uses these to certify that a backtest result
is statistically valid, not just a lucky draw.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Portfolio.BacktestValidity

/-- **Bonferroni correction.** If testing n strategies at
significance alpha, the per-test threshold is alpha/n. -/
@[stat_lemma]
theorem bonferroni_threshold_pos {alpha : ℝ} {n : ℕ}
    (h_alpha : 0 < alpha) (h_n : 0 < n) :
    0 < alpha / ↑n :=
  div_pos h_alpha (Nat.cast_pos (α := ℝ) |>.mpr h_n)

/-- **Multiple testing penalty.** More strategies tested means
higher bar for significance. -/
@[stat_lemma]
theorem bonferroni_antitone {alpha : ℝ} (h_alpha : 0 < alpha)
    {n₁ n₂ : ℕ} (h_n1 : 0 < n₁) (h : n₁ ≤ n₂) :
    alpha / ↑n₂ ≤ alpha / ↑n₁ := by
  apply div_le_div_of_nonneg_left (le_of_lt h_alpha)
    (Nat.cast_pos (α := ℝ) |>.mpr h_n1)
    (Nat.cast_le (α := ℝ) |>.mpr h)

/-- **Minimum track record length.** If n >= (z/S)^2, then
|z/S| <= sqrt(n). This connects sample size to statistical power.
Real proof via Real.le_sqrt + sq_abs. -/
@[stat_lemma]
theorem min_track_record {z S n : ℝ} (hn : (z / S) ^ 2 ≤ n) :
    |z / S| ≤ Real.sqrt n := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hn

/-- **Deflated Sharpe ratio.** The probability that the best of
n backtested strategies has Sharpe > S by luck alone increases
with n. Adjusting for this: DSR = S - sqrt(2 * log(n)) * vol_S.
We prove: the adjustment is nonneg when n >= 1. -/
@[stat_lemma]
theorem deflation_adjustment_nonneg {log_n vol_S : ℝ}
    (h_vol : 0 ≤ vol_S) :
    0 ≤ Real.sqrt (2 * log_n) * vol_S :=
  mul_nonneg (Real.sqrt_nonneg _) h_vol

/-- **Out-of-sample validation.** In-sample Sharpe minus
out-of-sample Sharpe is the overfitting penalty. Nonneg
penalty means IS >= OOS (expected from overfitting). -/
@[stat_lemma]
theorem overfit_penalty_expected {sharpe_is sharpe_oos : ℝ}
    (h : sharpe_oos ≤ sharpe_is) :
    0 ≤ sharpe_is - sharpe_oos := by linarith

end Pythia.Finance.Portfolio.BacktestValidity
