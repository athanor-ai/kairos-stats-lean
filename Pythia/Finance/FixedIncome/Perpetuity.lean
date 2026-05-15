/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Perpetuity Present Value

A perpetuity paying a constant cashflow `C` per period in perpetuity
under discount rate `r > 0` has present value

    PV(C, r) = C / r.

This is the classical Gordon-growth limit (with growth rate zero) and
the simplest closed-form fixed-income identity beyond the zero-coupon
bond.

## Main results

* `perpetuityValue`                : `PV(C, r) = C / r`
* `perpetuityValue_pos`            : `0 < PV` when `C > 0` and `r > 0`
* `perpetuityValue_nonneg`         : `0 ≤ PV` when `C ≥ 0` and `r > 0`
* `perpetuityValue_antitone_rate`  : antitone in `r` for `C ≥ 0`

## Why this lemma

Mathlib has `div_pos`, `div_nonneg`, `div_le_div_of_nonneg_left`,
but no named `perpetuity` declaration. Pythia surfaces the perpetuity
closed form so the `pythia` tactic cascade can close annuity / DCF
goals without the user reaching for the underlying division lemmas.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.2 (annuities and perpetuities).
* Gordon, M. J. "Dividends, Earnings, and Stock Prices."
  *Review of Economics and Statistics* 41(2): 99-105 (1959).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Present value of a perpetuity paying constant cashflow `C` per
period under discount rate `r`: `PV = C / r`. -/
noncomputable def perpetuityValue (C r : ℝ) : ℝ :=
  C / r

/-- **Positivity.** For positive cashflow and positive discount rate,
the perpetuity value is strictly positive. -/
@[stat_lemma]
theorem perpetuityValue_pos {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    0 < perpetuityValue C r := by
  unfold perpetuityValue; exact div_pos hC hr

/-- **Non-negativity.** For non-negative cashflow and positive
discount rate, the perpetuity value is non-negative. -/
@[stat_lemma]
theorem perpetuityValue_nonneg {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) :
    0 ≤ perpetuityValue C r := by
  unfold perpetuityValue; exact div_nonneg hC hr.le

/-- **Antitone in discount rate.** For non-negative cashflow and
strictly positive rates, the perpetuity value is non-increasing in
the discount rate. -/
@[stat_lemma]
theorem perpetuityValue_antitone_rate {C : ℝ} (hC : 0 ≤ C)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂) :
    perpetuityValue C r₂ ≤ perpetuityValue C r₁ := by
  unfold perpetuityValue
  exact div_le_div_of_nonneg_left hC hr₁ hr

end Pythia.Finance
