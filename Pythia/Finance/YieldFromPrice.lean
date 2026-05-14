/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Yield from Zero-Coupon Bond Price (Inverse of `bondZeroCoupon`)

The continuously-compounded zero-coupon yield implied by a bond
price `B`, face value `F`, and maturity `T > 0` is

    y(B, F, T) = -log(B / F) / T.

This inverts `Pythia.Finance.bondZeroCoupon`: under the meaningful
domain `0 < B ≤ F`, `0 < T`, plugging the implied yield back into
`bondZeroCoupon F · T` recovers the input price `B`.

## Main results

* `yieldFromPrice`               : `-log(B/F) / T`
* `yieldFromPrice_nonneg`        : `0 ≤ y` when `0 < B ≤ F` and `0 < T`
* `yieldFromPrice_zero_at_par`   : `B = F` (par bond) ⟹ `y = 0`
* `bondZeroCoupon_yieldFromPrice`:
  `bondZeroCoupon F (yieldFromPrice B F T) T = B` for `0 < B`, `0 < F`, `0 < T`

## Why this lemma

Mathlib has `Real.log_div`, `Real.exp_log`, `Real.log_pos`, but no
named `yield_from_price` declaration.  Pythia surfaces the inverse
function so the `pythia` tactic cascade can close yield-curve
bootstrap / implied-rate goals without re-deriving the log inversion.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.3 (zero-coupon yields from bond prices).
-/
import Mathlib
import Pythia.Finance.BondZeroCoupon
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Continuously-compounded zero-coupon yield implied by bond price
`B`, face value `F`, and maturity `T`: `y = -log(B/F) / T`. -/
noncomputable def yieldFromPrice (B F T : ℝ) : ℝ :=
  -(Real.log (B / F)) / T

/-- **Non-negativity for non-premium bonds.** When `0 < B ≤ F` (the
bond trades at or below par) and `0 < T`, the implied yield is
non-negative. -/
@[stat_lemma]
theorem yieldFromPrice_nonneg
    {B F T : ℝ} (hB : 0 < B) (hBF : B ≤ F) (hT : 0 < T) :
    0 ≤ yieldFromPrice B F T := by
  unfold yieldFromPrice
  have hF : 0 < F := lt_of_lt_of_le hB hBF
  have hBF1 : B / F ≤ 1 := (div_le_one hF).mpr hBF
  have hBF0 : 0 < B / F := div_pos hB hF
  have hlog_nonpos : Real.log (B / F) ≤ 0 := Real.log_nonpos hBF0.le hBF1
  have hneg : 0 ≤ -(Real.log (B / F)) := neg_nonneg.mpr hlog_nonpos
  exact div_nonneg hneg hT.le

/-- **Par bond has zero yield.** A bond trading at face value
(`B = F`, `F > 0`) has zero implied yield for any maturity. -/
@[stat_lemma]
theorem yieldFromPrice_zero_at_par
    {F T : ℝ} (hF : 0 < F) :
    yieldFromPrice F F T = 0 := by
  unfold yieldFromPrice
  rw [div_self hF.ne', Real.log_one, neg_zero, zero_div]

/-- **Round-trip.** Plugging the implied yield back into the
zero-coupon bond pricing function recovers the input price `B`,
provided `0 < B`, `0 < F`, `0 < T`. -/
theorem bondZeroCoupon_yieldFromPrice
    {B F T : ℝ} (hB : 0 < B) (hF : 0 < F) (hT : 0 < T) :
    bondZeroCoupon F (yieldFromPrice B F T) T = B := by
  unfold bondZeroCoupon yieldFromPrice
  have hBF : 0 < B / F := div_pos hB hF
  rw [div_mul_cancel₀ _ hT.ne', neg_neg, Real.exp_log hBF, mul_div_cancel₀ B hF.ne']

end Pythia.Finance
