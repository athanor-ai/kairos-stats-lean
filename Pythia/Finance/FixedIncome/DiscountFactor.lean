/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous-Compounding Discount Factor

The discount factor that converts a payoff at time `T` into its
present value under continuously-compounded rate `r` is

    D(r, T) = exp(-r · T).

This is the multiplicative inverse of the compound factor `exp(r · T)`
used in `Pythia.Finance.CompoundInterest`.  It is the building block
of present-value calculations across fixed income, derivatives, and
risk-neutral pricing.

## Main results

* `discountFactor`                : `D(r, T) = exp(-r·T)`
* `discountFactor_pos`            : `0 < discountFactor r T`
* `discountFactor_zero_time`      : `discountFactor r 0 = 1`
* `discountFactor_zero_rate`      : `discountFactor 0 T = 1`
* `discountFactor_antitone_rate`  : antitone in `r` for `T ≥ 0`
* `discountFactor_antitone_time`  : antitone in `T` for `r ≥ 0`
* `discountFactor_le_one`         : `discountFactor r T ≤ 1` for `r·T ≥ 0`

## Why this lemma

Mathlib has `Real.exp_pos`, `Real.exp_zero`, `Real.exp_le_exp`,
`Real.exp_neg`, but no named `discount_factor` declaration.  Pythia
exposes the continuously-compounded discount factor and its
monotonicity / boundary properties so the `pythia` tactic cascade can
close present-value goals without the user reaching for the
underlying real-analysis lemmas directly.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.2 (continuous compounding & discount factors).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Continuous-compounding discount factor:
    `D(r, T) = exp(-r · T)`. -/
noncomputable def discountFactor (r T : ℝ) : ℝ :=
  Real.exp (-(r * T))

/-- **Positivity.** The discount factor is strictly positive at any
rate and any horizon. -/
@[stat_lemma]
theorem discountFactor_pos (r T : ℝ) : 0 < discountFactor r T := by
  unfold discountFactor; exact Real.exp_pos _

/-- **Boundary at `T = 0`.** At zero horizon the discount factor is 1
(no discounting). -/
@[stat_lemma]
theorem discountFactor_zero_time (r : ℝ) : discountFactor r 0 = 1 := by
  unfold discountFactor; simp [mul_zero, neg_zero, Real.exp_zero]

/-- **Boundary at `r = 0`.** With zero rate the discount factor is 1
(no discounting). -/
@[stat_lemma]
theorem discountFactor_zero_rate (T : ℝ) : discountFactor 0 T = 1 := by
  unfold discountFactor; simp [zero_mul, neg_zero, Real.exp_zero]

/-- **Antitone in rate.** For non-negative horizon, the discount
factor is non-increasing in the rate: higher rates discount more
heavily. -/
@[stat_lemma]
theorem discountFactor_antitone_rate {T : ℝ} (hT : 0 ≤ T)
    {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    discountFactor r₂ T ≤ discountFactor r₁ T := by
  unfold discountFactor
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hr hT))

/-- **Antitone in horizon.** For non-negative rate, the discount
factor is non-increasing in the horizon: longer horizons discount
more heavily. -/
@[stat_lemma]
theorem discountFactor_antitone_time {r : ℝ} (hr : 0 ≤ r)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    discountFactor r T₂ ≤ discountFactor r T₁ := by
  unfold discountFactor
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hT hr))

/-- **Bounded above by 1.** When `r · T ≥ 0`, the discount factor is
at most 1 (the "no discounting" upper limit). -/
@[stat_lemma]
theorem discountFactor_le_one {r T : ℝ} (h : 0 ≤ r * T) :
    discountFactor r T ≤ 1 := by
  unfold discountFactor
  have : -(r * T) ≤ 0 := by linarith
  calc Real.exp (-(r * T)) ≤ Real.exp 0 := Real.exp_le_exp.mpr this
    _ = 1 := Real.exp_zero

end Pythia.Finance
