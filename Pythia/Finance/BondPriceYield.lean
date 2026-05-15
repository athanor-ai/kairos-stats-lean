/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bond Price-Yield Relationship (Zero-Coupon)

For a zero-coupon bond with face value `FV`, continuously-compounded
yield `y`, and time to maturity `T`, the price is

    P(y) = FV * exp(-y * T).

This module formalizes the core properties of this price-yield
relationship: strict positivity, boundary at zero maturity, the
classical inverse price-yield relation (higher yield implies lower
price), and monotonicity of price in face value.

## Main results

* `bondPrice`                   : `FV * exp(-y * T)`
* `bondPrice_pos`               : `0 < bondPrice FV y T` when `FV > 0`
* `bondPrice_zero_maturity`     : `bondPrice FV y 0 = FV`
* `bondPrice_antitone_yield`    : antitone in yield for `FV > 0`, `T >= 0`
* `bondPrice_mono_face`         : monotone in face value for fixed `y`, `T`
* `bondPrice_at_zero_yield`     : `bondPrice FV 0 T = FV`

## Why this lemma

Mathlib has `Real.exp_pos`, `Real.exp_le_exp`, `Real.exp_zero`, and
related real-analysis lemmas, but no named `bond_price` or
`bond_price_yield` declaration.  Pythia surfaces the zero-coupon
price-yield formula and its monotonicity properties so the `pythia`
tactic cascade can close fixed-income pricing and sensitivity goals
without requiring the user to manually unfold exponential identities.

## References

* Tuckman, B. and Serrat, A. *Fixed Income Securities.*
  Wiley (2011), Chapter 1 (prices, discount factors, and arbitrage).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Price of a zero-coupon bond with face value `FV`, continuously-
compounded yield `y`, and time to maturity `T`:
`P(y) = FV * exp(-y * T)`. -/
noncomputable def bondPrice (FV y T : ℝ) : ℝ :=
  FV * Real.exp (-(y * T))

/-- **Positivity.** For positive face value, the bond price is
strictly positive at any yield and any maturity. -/
@[stat_lemma]
theorem bondPrice_pos {FV : ℝ} (hFV : 0 < FV) (y T : ℝ) :
    0 < bondPrice FV y T := by
  unfold bondPrice
  exact mul_pos hFV (Real.exp_pos _)

/-- **Boundary at `T = 0`.** A bond maturing immediately prices at
face value: `bondPrice FV y 0 = FV`. -/
@[stat_lemma]
theorem bondPrice_zero_maturity (FV y : ℝ) :
    bondPrice FV y 0 = FV := by
  unfold bondPrice
  simp [mul_zero, neg_zero, Real.exp_zero]

/-- **Inverse price-yield relation.** For positive face value and
non-negative maturity, the bond price is antitone in yield: a higher
yield produces a weakly lower price.  This is the sign underlying
classical bond duration. -/
@[stat_lemma]
theorem bondPrice_antitone_yield {FV T : ℝ} (hFV : 0 < FV) (hT : 0 ≤ T)
    {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    bondPrice FV y₂ T ≤ bondPrice FV y₁ T := by
  unfold bondPrice
  apply mul_le_mul_of_nonneg_left _ hFV.le
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hy hT))

/-- **Monotonicity in face value.** For fixed yield and maturity, the
bond price is monotone (non-decreasing) in face value. -/
@[stat_lemma]
theorem bondPrice_mono_face (y T : ℝ) {FV₁ FV₂ : ℝ} (h : FV₁ ≤ FV₂) :
    bondPrice FV₁ y T ≤ bondPrice FV₂ y T := by
  unfold bondPrice
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- **Zero-yield boundary.** At zero yield, the bond prices at face
value regardless of maturity: `bondPrice FV 0 T = FV`. -/
@[stat_lemma]
theorem bondPrice_at_zero_yield (FV T : ℝ) :
    bondPrice FV 0 T = FV := by
  unfold bondPrice
  simp [zero_mul, neg_zero, Real.exp_zero]

end Pythia.Finance
