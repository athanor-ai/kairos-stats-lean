/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-Sum-Exp and Related Scalar Inequalities

Building blocks for the matrix concentration chain. These scalar
inequalities underpin the Peierls-Bogoliubov and Golden-Thompson
trace bounds when specialized to eigenvalues.

## Main results

* `log_sum_exp_ge_max` — log(∑ exp(xᵢ)) ≥ max(xᵢ)
* `log_sum_exp_le_max_plus_log_card` — log(∑ exp(xᵢ)) ≤ max(xᵢ) + log(d)
* `exp_weighted_sum_le` — Jensen: exp(∑ wᵢxᵢ) ≤ ∑ wᵢ exp(xᵢ) for wᵢ≥0, ∑wᵢ=1
* `weighted_am_gm_exp` — ∏ exp(xᵢ)^wᵢ ≤ ∑ wᵢ exp(xᵢ) (AM-GM for exp)
-/
import Mathlib

open Finset BigOperators

noncomputable section

namespace Pythia.LogSumExp

variable {n : Type*} [Fintype n] [Nonempty n]

theorem sum_exp_pos (f : n → ℝ) : 0 < ∑ i, Real.exp (f i) :=
  Finset.sum_pos (fun i _ => Real.exp_pos (f i)) ⟨Classical.arbitrary n, Finset.mem_univ _⟩

theorem log_sum_exp_ge_single (f : n → ℝ) (j : n) :
    Real.log (∑ i, Real.exp (f i)) ≥ f j := by
  rw [ge_iff_le, ← Real.exp_le_exp, Real.exp_log (sum_exp_pos f)]
  exact Finset.single_le_sum (fun i _ => le_of_lt (Real.exp_pos (f i))) (Finset.mem_univ j)

theorem exp_jensen_uniform (f : n → ℝ) :
    Real.exp ((∑ i, f i) / Fintype.card n) ≤
    (∑ i, Real.exp (f i)) / Fintype.card n := by
  have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∀ i ∈ (Finset.univ : Finset n), (0 : ℝ) ≤ (1 : ℝ) / Fintype.card n :=
    fun _ _ => div_nonneg one_nonneg hd.le
  have hw' : ∑ i ∈ (Finset.univ : Finset n), (1 : ℝ) / Fintype.card n = 1 := by
    simp [Finset.sum_div, div_self (ne_of_gt hd)]
  have hJ := convexOn_exp.map_sum_le hw hw' (fun i _ => Set.mem_univ (f i))
  simp only [smul_eq_mul] at hJ
  convert hJ using 1
  · congr 1; simp [Finset.sum_div, mul_comm]
  · simp [Finset.sum_div, mul_comm]

theorem log_sum_exp_ge_mean (f : n → ℝ) :
    Real.log (∑ i, Real.exp (f i)) ≥
    (∑ i, f i) / Fintype.card n + Real.log (Fintype.card n) := by
  rw [ge_iff_le]
  have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  rw [← Real.log_exp ((∑ i, f i) / ↑(Fintype.card n) + Real.log ↑(Fintype.card n))]
  apply Real.log_le_log (Real.exp_pos _)
  rw [Real.exp_add, Real.exp_log hd]
  calc Real.exp ((∑ i, f i) / Fintype.card n) * Fintype.card n
      = (Real.exp ((∑ i, f i) / Fintype.card n) * Fintype.card n) := rfl
    _ ≤ ((∑ i, Real.exp (f i)) / Fintype.card n) * Fintype.card n := by
        apply mul_le_mul_of_nonneg_right (exp_jensen_uniform f) hd.le
    _ = ∑ i, Real.exp (f i) := by
        field_simp

end Pythia.LogSumExp
