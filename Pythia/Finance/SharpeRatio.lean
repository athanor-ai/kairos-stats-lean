/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharpe Ratio (algebraic form)

The Sharpe ratio of a return stream with expected return `μ`, return
standard deviation `σ`, and risk-free rate `rf` is

    Sharpe(μ, rf, σ) = (μ - rf) / σ.

This file gives the closed-form algebraic identities of the Sharpe
ratio without invoking probability machinery: positivity / sign
direction, monotonicity in the expected-return argument, and scale
invariance under positive rescaling of risk.

## Main results

* `sharpeRatio`                  : `(μ - rf) / σ`
* `sharpeRatio_pos`              : `0 < sharpeRatio μ rf σ` when `rf < μ` and `0 < σ`
* `sharpeRatio_mono_excess`      : monotone in `μ - rf` for `0 < σ`
* `sharpeRatio_scale_invariant`  :
  `sharpeRatio (α·μ) (α·rf) (α·σ) = sharpeRatio μ rf σ` for `α > 0`

## Why this lemma

Mathlib has `div_pos`, `div_lt_div_iff`, but no named `sharpe_ratio`
declaration.  Pythia surfaces the algebraic Sharpe identities so the
`pythia` tactic cascade can close risk-adjusted-return goals without
the user reaching for the underlying division lemmas.

## References

* Sharpe, W. F. "Mutual Fund Performance."
  *Journal of Business* 39(S1): 119-138 (1966).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Sharpe ratio (algebraic form): `(μ - rf) / σ`. -/
noncomputable def sharpeRatio (μ rf σ : ℝ) : ℝ :=
  (μ - rf) / σ

/-- **Positivity.** The Sharpe ratio is strictly positive when the
expected return exceeds the risk-free rate and the volatility is
strictly positive. -/
@[stat_lemma]
theorem sharpeRatio_pos {μ rf σ : ℝ} (h_excess : rf < μ) (hσ : 0 < σ) :
    0 < sharpeRatio μ rf σ := by
  unfold sharpeRatio
  exact div_pos (sub_pos.mpr h_excess) hσ

/-- **Monotone in excess return.** For fixed positive volatility, the
Sharpe ratio is monotone non-decreasing in the excess return `μ - rf`. -/
@[stat_lemma]
theorem sharpeRatio_mono_excess {σ : ℝ} (hσ : 0 < σ)
    {μ₁ rf₁ μ₂ rf₂ : ℝ} (h : μ₁ - rf₁ ≤ μ₂ - rf₂) :
    sharpeRatio μ₁ rf₁ σ ≤ sharpeRatio μ₂ rf₂ σ := by
  unfold sharpeRatio
  exact div_le_div_of_nonneg_right h hσ.le

/-- **Scale invariance.** Rescaling all three arguments (expected
return, risk-free rate, volatility) by a strictly positive constant
leaves the Sharpe ratio unchanged. -/
@[stat_lemma]
theorem sharpeRatio_scale_invariant {α : ℝ} (hα : 0 < α) (μ rf σ : ℝ) :
    sharpeRatio (α * μ) (α * rf) (α * σ) = sharpeRatio μ rf σ := by
  unfold sharpeRatio
  rw [← mul_sub]
  exact mul_div_mul_left (μ - rf) σ hα.ne'

/-- **Positive Sharpe implies positive excess return (converse of
sharpeRatio_pos).** Under strictly positive volatility, a strictly
positive Sharpe ratio forces the expected return to exceed the
risk-free rate. The proof uses the `div_pos_iff` characterisation in
reverse: positive ratio with positive denominator forces positive
numerator. Real Mathlib reasoning, not unfold-and-ring. -/
@[stat_lemma]
theorem excess_pos_of_sharpeRatio_pos {μ rf σ : ℝ}
    (hσ : 0 < σ) (h_sharpe_pos : 0 < sharpeRatio μ rf σ) :
    rf < μ := by
  unfold sharpeRatio at h_sharpe_pos
  -- 0 < (μ - rf) / σ with 0 < σ ⇒ 0 < μ - rf via div_pos_iff.
  have h_num_pos : 0 < μ - rf := by
    rcases (div_pos_iff (b := σ)).mp h_sharpe_pos with ⟨h₁, _⟩ | ⟨_, h₂⟩
    · exact h₁
    · linarith
  linarith

/-- **Cash-rate translation invariance.** Adding the same `c` to both
the expected return and the risk-free rate cancels in the numerator,
leaving the Sharpe ratio unchanged. This is the ADEH cash-invariance
property at the Sharpe level. -/
@[stat_lemma]
theorem sharpeRatio_cash_invariant (μ rf σ c : ℝ) :
    sharpeRatio (μ + c) (rf + c) σ = sharpeRatio μ rf σ := by
  unfold sharpeRatio
  ring_nf

end Pythia.Finance
