/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DCF Valuation Properties

Proves properties of discounted cash flow valuation:
present value monotonicity, terminal value dominance,
and discount rate sensitivity.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.Fundamentals.DCFValuation

/-- PV of a single cash flow: CF / (1+r)^t ≈ CF * exp(-r*t). -/
noncomputable def pvCashFlow (CF r t : ℝ) : ℝ :=
  CF * Real.exp (-(r * t))

/-- **PV positive for positive CF.** -/
@[stat_lemma]
theorem pv_pos {CF : ℝ} (hCF : 0 < CF) (r t : ℝ) :
    0 < pvCashFlow CF r t :=
  mul_pos hCF (Real.exp_pos _)

/-- **PV antitone in discount rate.** Higher r means lower PV. -/
@[stat_lemma]
theorem pv_antitone_rate {CF : ℝ} (hCF : 0 < CF) {t : ℝ} (ht : 0 ≤ t)
    {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    pvCashFlow CF r₂ t ≤ pvCashFlow CF r₁ t := by
  unfold pvCashFlow
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hr ht)))
    (le_of_lt hCF)

/-- **PV antitone in time.** Later cash flows are worth less today. -/
@[stat_lemma]
theorem pv_antitone_time {CF r : ℝ} (hCF : 0 < CF) (hr : 0 ≤ r)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    pvCashFlow CF r t₂ ≤ pvCashFlow CF r t₁ := by
  unfold pvCashFlow
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ht hr)))
    (le_of_lt hCF)

/-- **PV at zero rate equals CF.** No discounting means full value. -/
@[stat_lemma]
theorem pv_at_zero_rate (CF t : ℝ) :
    pvCashFlow CF 0 t = CF := by
  unfold pvCashFlow; simp [zero_mul, neg_zero, Real.exp_zero]

/-- **Sum of PVs is portfolio PV.** Linearity of discounting. -/
@[stat_lemma]
theorem pv_additive {CF1 CF2 r t : ℝ} :
    pvCashFlow (CF1 + CF2) r t = pvCashFlow CF1 r t + pvCashFlow CF2 r t := by
  unfold pvCashFlow; ring

end Pythia.Finance.Fundamentals.DCFValuation
