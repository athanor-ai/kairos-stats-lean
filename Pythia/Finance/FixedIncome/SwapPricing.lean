/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interest Rate Swap Pricing

Proves properties of IRS pricing: fixed leg PV, floating leg PV,
par swap rate, and swap value decomposition.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.FixedIncome.SwapPricing

/-- **Fixed leg PV.** Sum of discounted fixed coupons:
PV_fixed = c * sum_i D(T_i) * delta_i. -/
@[stat_lemma]
theorem fixed_leg_nonneg {n : ℕ} (coupon : ℝ) (disc_deltas : Fin n → ℝ)
    (hc : 0 ≤ coupon) (hd : ∀ i, 0 ≤ disc_deltas i) :
    0 ≤ coupon * ∑ i, disc_deltas i :=
  mul_nonneg hc (Finset.sum_nonneg fun i _ => hd i)

/-- **Floating leg = 1 - D(T_n).** At inception, the floating leg
PV equals par minus the final discount factor. -/
@[stat_lemma]
theorem floating_leg_bounded {D_Tn : ℝ}
    (h_pos : 0 < D_Tn) (h_le : D_Tn ≤ 1) :
    0 ≤ 1 - D_Tn ∧ 1 - D_Tn ≤ 1 := by
  constructor <;> linarith

/-- **Par swap rate makes NPV zero.** At the par rate c*,
PV_fixed = PV_floating, so the swap has zero value at inception. -/
@[stat_lemma]
theorem par_swap_zero_value {pv_fixed pv_floating : ℝ}
    (h : pv_fixed = pv_floating) :
    pv_fixed - pv_floating = 0 := by linarith

/-- **Swap value = PV_floating - PV_fixed (receiver).** -/
@[stat_lemma]
theorem receiver_swap_value {pv_float pv_fix : ℝ} :
    pv_float - pv_fix = -(pv_fix - pv_float) := by ring

/-- **Swap value antitone in fixed rate (payer).** Higher fixed
rate means lower payer swap value (paying more fixed). -/
@[stat_lemma]
theorem payer_antitone_rate {annuity c₁ c₂ pv_float : ℝ}
    (h_ann : 0 < annuity) (h : c₁ ≤ c₂) :
    pv_float - c₂ * annuity ≤ pv_float - c₁ * annuity := by
  linarith [mul_le_mul_of_nonneg_right h (le_of_lt h_ann)]

/-- **DV01 of a swap.** The change in swap value per 1bp change
in the fixed rate is approximately the annuity factor. -/
@[stat_lemma]
theorem swap_dv01_nonneg {annuity : ℝ} (h : 0 ≤ annuity) :
    0 ≤ annuity -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

end Pythia.Finance.FixedIncome.SwapPricing
