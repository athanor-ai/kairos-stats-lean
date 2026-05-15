/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Macaulay Duration and Convexity for Zero-Coupon Bonds

For a zero-coupon bond paying face `F` at maturity `T` under
continuously-compounded yield `y`, the *Macaulay duration* equals
the time-to-maturity:

    D_Mac(F, y, T) = T,

and the convexity (second-derivative-of-log-price-in-yield, scaled)
equals `T²`:

    Conv(F, y, T) = T².

This file gives the algebraic identities (definitions are just
projections onto `T`/`T²`); the derivative-based interpretation
matches the calculus of `Pythia.Finance.bondZeroCoupon`:
`-(d/dy) log(B) = T = D_Mac` and `(d²/dy²) log(B) = T² = Conv`.

For coupon-bearing bonds, Macaulay duration becomes a present-value-
weighted average of cashflow times; this module handles the
zero-coupon kernel, which is the building block for the general
case.

## Main results

* `macaulayZeroCoupon`            : `T` (Macaulay duration = maturity)
* `convexityZeroCoupon`           : `T²`
* `modifiedDurationContinuous`    : `T` (under continuous compounding,
  modified = Macaulay)
* `macaulay_nonneg`               : `0 ≤ T → 0 ≤ D_Mac`
* `convexity_nonneg`              : `0 ≤ Conv` unconditionally
* `convexity_eq_dur_sq`           : `Conv = D_Mac²`

## Why this lemma

Macaulay duration is the rate-sensitivity measure of fixed-income
portfolios.  Together with convexity it gives the first- and
second-order Taylor approximation of bond price under yield shifts —
the bedrock of fixed-income risk management.  Surfacing the
zero-coupon identities in Pythia gives the `pythia` tactic cascade
a clean closure target for fixed-income sensitivity goals.

## References

* Macaulay, F. R. *Some Theoretical Problems Suggested by the
  Movements of Interest Rates, Bond Yields, and Stock Prices in the
  United States Since 1856.* NBER (1938).
* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.9-§4.10 (duration and convexity).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Macaulay duration of a zero-coupon bond paying face `F` at
maturity `T` under continuously-compounded yield `y`:
`D_Mac = T`. -/
noncomputable def macaulayZeroCoupon (F y T : ℝ) : ℝ := T

/-- Convexity of a zero-coupon bond: `Conv = T²`. -/
noncomputable def convexityZeroCoupon (F y T : ℝ) : ℝ := T^2

/-- Modified duration of a zero-coupon bond under continuous
compounding: identical to Macaulay duration (`D_mod = D_Mac` for
continuous compounding). -/
noncomputable def modifiedDurationContinuous (F y T : ℝ) : ℝ := T

/-- **Macaulay non-negativity.** For non-negative maturity. -/
@[stat_lemma]
theorem macaulay_nonneg {T : ℝ} (hT : 0 ≤ T) (F y : ℝ) :
    0 ≤ macaulayZeroCoupon F y T := by
  unfold macaulayZeroCoupon; exact hT

/-- **Convexity non-negativity (unconditional).**
The square `T²` is always non-negative. -/
@[stat_lemma]
theorem convexity_nonneg (F y T : ℝ) :
    0 ≤ convexityZeroCoupon F y T := by
  unfold convexityZeroCoupon; exact sq_nonneg T

/-- **Convexity equals duration squared (zero-coupon identity).**
The convexity-duration relationship `Conv = D_Mac²` is the algebraic
backbone of the second-order Taylor approximation of bond price
under yield shifts. -/
@[stat_lemma]
theorem convexity_eq_dur_sq (F y T : ℝ) :
    convexityZeroCoupon F y T
      = (macaulayZeroCoupon F y T) ^ 2 := by
  unfold convexityZeroCoupon macaulayZeroCoupon; rfl

end Pythia.Finance
