/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Square-Root-Time Volatility Scaling

Under the random-walk (independent log-returns) model, daily
volatility `σ_d` scales to volatility over `n` days as

    σ_n = σ_d · √n.

This is the *√t-scaling rule* used universally by quantitative
practitioners to annualise / de-annualise volatilities across
sampling frequencies.  The closed-form identity is purely algebraic
once we work with the variance:

    variance_n = variance_d · n,    so    σ_n = σ_d · √n.

## Main results

* `volatilityScale`                : `σ_d · √n` for `n : ℝ`
* `volatilityScale_zero_horizon`   : at `n = 0` → 0
* `volatilityScale_unit_horizon`   : at `n = 1` → `σ_d`
* `volatilityScale_monotone`       : monotone in horizon `n ≥ 0` for `σ_d ≥ 0`
* `volatilityScale_squared`        : `(σ_d · √n)² = σ_d² · n` for `n ≥ 0`
  (variance scales linearly in time)

## Why this lemma

Volatility-scaling is the bedrock of risk-engine calibration:
practitioners estimate intraday σ at 1-second or 1-minute frequency,
then scale to daily / annual horizons for risk reporting.  Errors
here propagate to VaR / ES / position-limit calculations.  Surfacing
the identity in Pythia gives the `pythia` cascade a clean closure
target for sampling-frequency conversions.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §22.2 (volatility-time scaling for IID returns).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Volatility-scaled to `n`-period horizon under the IID-returns
model:  `σ_n = σ_d · √n`. -/
noncomputable def volatilityScale (σ_d n : ℝ) : ℝ :=
  σ_d * Real.sqrt n

/-- **Zero horizon.** Volatility over zero time is zero. -/
@[stat_lemma]
theorem volatilityScale_zero_horizon (σ_d : ℝ) :
    volatilityScale σ_d 0 = 0 := by
  unfold volatilityScale; simp [Real.sqrt_zero, mul_zero]

/-- **Unit horizon.** Volatility over one period equals the base
volatility. -/
@[stat_lemma]
theorem volatilityScale_unit_horizon (σ_d : ℝ) :
    volatilityScale σ_d 1 = σ_d := by
  unfold volatilityScale; simp [Real.sqrt_one, mul_one]

/-- **Monotone in horizon.** For non-negative base volatility, the
scaled volatility is monotone non-decreasing in the horizon. -/
@[stat_lemma]
theorem volatilityScale_monotone {σ_d : ℝ} (hσ : 0 ≤ σ_d)
    {n₁ n₂ : ℝ} (hn₁ : 0 ≤ n₁) (hn : n₁ ≤ n₂) :
    volatilityScale σ_d n₁ ≤ volatilityScale σ_d n₂ := by
  unfold volatilityScale
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hn) hσ

/-- **Variance scales linearly in time.** Squaring the scaled
volatility recovers the linear-in-time variance:

    (σ_d · √n)² = σ_d² · n    (for `n ≥ 0`).

This is the algebraic kernel of the √t-scaling rule. -/
@[stat_lemma]
theorem volatilityScale_squared {σ_d n : ℝ} (hn : 0 ≤ n) :
    (volatilityScale σ_d n)^2 = σ_d^2 * n := by
  unfold volatilityScale
  rw [mul_pow, Real.sq_sqrt hn]

end Pythia.Finance
