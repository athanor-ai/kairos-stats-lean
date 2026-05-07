/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Peierls–Bogoliubov Inequality (Jensen form)

For a Hermitian matrix A of dimension d with eigenvalues λ₁, ..., λ_d:

  (1/d) · tr(exp(A)) ≥ exp((1/d) · tr(A))

equivalently:  (1/d) ∑ᵢ exp(λᵢ) ≥ exp((1/d) ∑ᵢ λᵢ)

This is Jensen's inequality for the convex function exp applied to
eigenvalues with uniform weight 1/d.

## Proof

Uses `convexOn_exp.map_sum_le` (Jensen's inequality in Mathlib)
with uniform weights w_i = 1/d and values x_i = λ_i.

## Main results

* `sum_exp_div_ge_exp_sum_div` — (1/d)∑exp(λᵢ) ≥ exp((1/d)∑λᵢ)
* `trace_exp_div_ge_exp_trace_div` — connects to Hermitian matrix trace
-/
import Mathlib
import Pythia.Frontier.MatrixLieb

open Finset BigOperators

noncomputable section

namespace Pythia.PeierlsBogoliubov

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem sum_exp_div_ge_exp_sum_div (f : n → ℝ) :
    (∑ i, Real.exp (f i)) / Fintype.card n ≥
    Real.exp ((∑ i, f i) / Fintype.card n) := by
  have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  rw [ge_iff_le]
  have hw : ∀ i ∈ (Finset.univ : Finset n), (0 : ℝ) ≤ (1 : ℝ) / Fintype.card n :=
    fun _ _ => div_nonneg one_nonneg (Nat.cast_nonneg)
  have hw' : ∑ i ∈ (Finset.univ : Finset n), (1 : ℝ) / Fintype.card n = 1 := by
    simp [Finset.sum_div, Finset.card_univ, div_self (ne_of_gt hd)]
  have hJ := convexOn_exp.map_sum_le hw hw' (fun i _ => Set.mem_univ (f i))
  simp only [smul_eq_mul] at hJ
  rw [show ∑ i ∈ Finset.univ, 1 / ↑(Fintype.card n) * f i =
      (∑ i, f i) / Fintype.card n by
    simp [Finset.sum_div, mul_comm]] at hJ
  rw [show ∑ i ∈ Finset.univ, 1 / ↑(Fintype.card n) * Real.exp (f i) =
      (∑ i, Real.exp (f i)) / Fintype.card n by
    simp [Finset.sum_div, mul_comm]] at hJ
  exact hJ

theorem trace_eigenvalues_eq (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i : ℂ)) = A.trace :=
  hA.trace_eq_sum_eigenvalues.symm

theorem trace_exp_div_ge_exp_trace_div
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (∑ i, Real.exp (hA.eigenvalues i)) / Fintype.card n ≥
    Real.exp ((∑ i, hA.eigenvalues i) / Fintype.card n) :=
  sum_exp_div_ge_exp_sum_div hA.eigenvalues

end Pythia.PeierlsBogoliubov
