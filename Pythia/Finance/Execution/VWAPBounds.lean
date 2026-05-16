/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# VWAP Execution Bounds

Proves properties of volume-weighted average price execution.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Execution.VWAPBounds

/-- VWAP = sum(price_i * vol_i) / sum(vol_i). -/
noncomputable def vwap {n : ℕ} (prices volumes : Fin n → ℝ) : ℝ :=
  (∑ i, prices i * volumes i) / ∑ i, volumes i

/-- **VWAP between min and max price.** -/
@[stat_lemma]
theorem vwap_ge_min {n : ℕ} (prices volumes : Fin n → ℝ)
    (p_min : ℝ) (h_vol : ∀ i, 0 ≤ volumes i)
    (h_total : 0 < ∑ i, volumes i)
    (h_min : ∀ i, p_min ≤ prices i) :
    p_min ≤ vwap prices volumes := by
  unfold vwap
  rw [le_div_iff₀ h_total]
  calc p_min * ∑ i, volumes i
      = ∑ i, p_min * volumes i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, prices i * volumes i := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (h_min i) (h_vol i)

/-- **VWAP slippage = VWAP - arrival price.** Nonneg for buy orders
when VWAP exceeds arrival. -/
@[stat_lemma]
theorem vwap_slippage_nonneg {vwap_val arrival : ℝ}
    (h : arrival ≤ vwap_val) :
    0 ≤ vwap_val - arrival := by linarith

/-- **Participation-weighted VWAP.** If we trade proportion alpha
of each bucket's volume, our VWAP equals the market VWAP. -/
@[stat_lemma]
theorem participation_matches_vwap {n : ℕ}
    (prices volumes : Fin n → ℝ) (alpha : ℝ) (h_alpha : alpha ≠ 0)
    (h_vol : 0 < ∑ i, volumes i) :
    vwap prices (fun i => alpha * volumes i) = vwap prices volumes := by
  simp only [vwap]
  have h1 : ∑ i : Fin n, prices i * (alpha * volumes i)
      = alpha * ∑ i, prices i * volumes i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have h2 : ∑ i : Fin n, alpha * volumes i = alpha * ∑ i, volumes i := by
    rw [Finset.mul_sum]
  rw [h1, h2, mul_div_mul_left _ _ h_alpha]

end Pythia.Finance.Execution.VWAPBounds
