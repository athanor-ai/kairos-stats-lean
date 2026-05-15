/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Zero-Coupon Bond Price

A zero-coupon bond paying face `F` at maturity `T` discounted at
continuously-compounded yield `y` has present value

    B(F, y, T) = F · exp(-y · T).

This is the building block of fixed-income pricing.  The price is
*decreasing in yield* (the classical inverse price-yield relation
underlying the sign of bond duration) and *convex in yield* (the
foundation of bond-convexity-as-second-derivative).

## Main results

* `bondZeroCoupon`                       : present value `F · exp(-y·T)`
* `bondZeroCoupon_pos`                   : `0 < bondZeroCoupon F y T` when `F > 0`
* `bondZeroCoupon_zero_time`             : `bondZeroCoupon F y 0 = F`
* `bondZeroCoupon_antitone_yield`        : decreasing in yield `y` for `F ≥ 0`, `T ≥ 0`

## Why this lemma

Mathlib has `Real.exp_pos`, `Real.exp_le_exp`, and friends, but no
named `bond_price` or `discount_factor` declaration.  Pythia exposes
the zero-coupon bond price and its monotonicity property so the
`pythia` tactic cascade can close fixed-income / duration / convexity
goals without the user reaching for the underlying real-analysis
lemmas directly.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.4 (zero rates, bond pricing).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Present value of a zero-coupon bond paying face `F` at maturity
`T` under continuously-compounded yield `y`: `B(F, y, T) = F · exp(-y · T)`. -/
noncomputable def bondZeroCoupon (F y T : ℝ) : ℝ :=
  F * Real.exp (-(y * T))

/-- **Positivity.** For positive face value, the bond price is
strictly positive at any yield / maturity. -/
@[stat_lemma]
theorem bondZeroCoupon_pos {F : ℝ} (hF : 0 < F) (y T : ℝ) :
    0 < bondZeroCoupon F y T := by
  unfold bondZeroCoupon; exact mul_pos hF (Real.exp_pos _)

/-- **Boundary at `T = 0`.** A bond maturing at time zero pays face
value immediately: `bondZeroCoupon F y 0 = F`. -/
@[stat_lemma]
theorem bondZeroCoupon_zero_time (F y : ℝ) :
    bondZeroCoupon F y 0 = F := by
  unfold bondZeroCoupon; simp [mul_zero, neg_zero, Real.exp_zero]

/-- **Inverse price-yield relation.** For non-negative face value and
non-negative maturity, the bond price is *antitone* (non-increasing)
in the yield.  This is the sign underlying classical bond duration. -/
@[stat_lemma]
theorem bondZeroCoupon_antitone_yield {F T : ℝ} (hF : 0 ≤ F) (hT : 0 ≤ T)
    {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    bondZeroCoupon F y₂ T ≤ bondZeroCoupon F y₁ T := by
  unfold bondZeroCoupon
  apply mul_le_mul_of_nonneg_left _ hF
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hy hT))

end Pythia.Finance
