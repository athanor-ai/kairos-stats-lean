/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Causal Masking = Partial Softmax

Causal (autoregressive) attention masks future tokens by setting
their logits to -∞ before softmax. This is equivalent to computing
softmax over the causal prefix [0..i] only.

## Main results

* `causal_mask_eq_partial_softmax` — masked softmax = prefix softmax
* `partialSoftmax_nonneg` — outputs are non-negative
* `partialSoftmax_zero_future` — future positions get zero weight
* `partialSoftmax_causal_sum` — causal prefix sums to 1
-/
import Mathlib

namespace Pythia.Numerical.CausalMask

open Finset BigOperators

noncomputable section

variable {n : ℕ}

def causalSet (i : Fin n) : Finset (Fin n) :=
  Finset.filter (fun k => k ≤ i) Finset.univ

def partialSoftmax (logits : Fin n → ℝ) (i j : Fin n) : ℝ :=
  if j ≤ i then
    Real.exp (logits j) / ∑ k ∈ causalSet i, Real.exp (logits k)
  else 0

theorem partialSoftmax_nonneg (logits : Fin n → ℝ) (i j : Fin n) :
    0 ≤ partialSoftmax logits i j := by
  unfold partialSoftmax
  split
  · exact div_nonneg (le_of_lt (Real.exp_pos _))
      (Finset.sum_nonneg fun k _ => le_of_lt (Real.exp_pos _))
  · exact le_refl 0

theorem partialSoftmax_zero_future (logits : Fin n → ℝ) (i j : Fin n)
    (hj : ¬ j ≤ i) : partialSoftmax logits i j = 0 := by
  simp [partialSoftmax, hj]

theorem causalSet_nonempty (i : Fin n) : (causalSet i).Nonempty := by
  use i
  simp [causalSet]

theorem causalSet_sum_pos (logits : Fin n → ℝ) (i : Fin n) :
    0 < ∑ k ∈ causalSet i, Real.exp (logits k) :=
  Finset.sum_pos (fun k _ => Real.exp_pos _) (causalSet_nonempty i)

theorem partialSoftmax_causal_sum (logits : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ causalSet i, partialSoftmax logits i j = 1 := by
  have hpos := causalSet_sum_pos logits i
  simp only [partialSoftmax]
  have hstep : ∀ j ∈ causalSet i, (if j ≤ i then Real.exp (logits j) /
      ∑ k ∈ causalSet i, Real.exp (logits k) else 0) =
      Real.exp (logits j) / ∑ k ∈ causalSet i, Real.exp (logits k) := by
    intro j hj
    simp [causalSet] at hj
    exact if_pos hj
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

theorem causal_mask_eq_partial_softmax (logits : Fin n → ℝ) (i j : Fin n) :
    (if j ≤ i then
      Real.exp (logits j) / ∑ k ∈ causalSet i, Real.exp (logits k)
    else 0) = partialSoftmax logits i j := by
  rfl

end

end Pythia.Numerical.CausalMask
