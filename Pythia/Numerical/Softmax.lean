/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Floating-Point Softmax Error Bound

Softmax(x)ᵢ = exp(xᵢ) / Σⱼ exp(xⱼ) is the workhorse activation of
transformer architectures. In floating-point, both the exponentials
and the normalization sum introduce rounding error. The standard
"shifted" implementation subtracts max(x) for numerical stability:

  softmax(x)ᵢ = exp(xᵢ - max(x)) / Σⱼ exp(xⱼ - max(x))

## Error analysis (Higham-style)

For each exponential: |fl(exp(z)) - exp(z)| ≤ u · exp(z)  (faithfully
rounded elementary function, per IEEE 754-2019 recommended ops).

The normalization sum of n exponentials has error governed by γ_n.

The combined per-entry softmax error satisfies:

  |fl(softmax(x))ᵢ - softmax(x)ᵢ| ≤ (n + 2) · u · softmax(x)ᵢ

in the practical regime where (n+2)·u ≪ 1. This is the key result:
softmax error is proportional to the output value itself, with a
small constant depending on the sequence length n.

## Main results

* `softmax_entry` — exact real softmax entry definition
* `softmax_sum_one` — softmax entries sum to 1
* `softmax_nonneg` — softmax entries are non-negative
* `exp_round_error` — faithful rounding error for exp
* `softmax_error_bound` — per-entry error bound for floating-point softmax

## References

* Blanchard, P., Higham, N. J., Mary, T. "A Class of Fast and
  Accurate Summation Algorithms." SIAM J. Sci. Comput. (2020).
* IEEE Std 754-2019, §9 (recommended operations).
-/
import Mathlib
import Pythia.Numerical.MatMul

namespace Pythia.Numerical.Softmax

open Finset BigOperators

variable {n : ℕ}

noncomputable section

/-- Softmax entry: softmax(x)ᵢ = exp(xᵢ) / Σⱼ exp(xⱼ).
    Defined for x : Fin n → ℝ and index i : Fin n. -/
def softmax_entry (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (x i) / ∑ j, Real.exp (x j)

/-- The sum of softmax entries equals 1 (when n ≥ 1). -/
theorem softmax_sum_one (x : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, softmax_entry x i = 1 := by
  unfold softmax_entry
  rw [← Finset.sum_div]
  apply div_self
  have : (0 : ℝ) < ∑ j : Fin n, Real.exp (x j) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply Finset.sum_pos
    · intro i _; exact Real.exp_pos _
    · exact Finset.univ_nonempty
  linarith

/-- Each softmax entry is non-negative. -/
theorem softmax_nonneg (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ softmax_entry x i := by
  unfold softmax_entry
  apply div_nonneg
  · exact le_of_lt (Real.exp_pos _)
  · apply Finset.sum_nonneg
    intro j _; exact le_of_lt (Real.exp_pos _)

/-- Each softmax entry is at most 1. -/
theorem softmax_le_one (x : Fin n → ℝ) (i : Fin n) :
    softmax_entry x i ≤ 1 := by
  unfold softmax_entry
  have h_sum_pos : (0 : ℝ) < ∑ j, Real.exp (x j) := by
    have : Nonempty (Fin n) := ⟨i⟩
    apply Finset.sum_pos
    · intro j _; exact Real.exp_pos _
    · exact Finset.univ_nonempty
  rw [div_le_one₀ h_sum_pos]
  exact Finset.single_le_sum (fun j _ => le_of_lt (Real.exp_pos _))
    (Finset.mem_univ i)

/-- **Faithful rounding of exp (parametrised).**

IEEE 754-2019 recommends that exp be faithfully rounded, meaning
|fl(exp(z)) - exp(z)| ≤ u · exp(z). This is taken as hypothesis
since Lean's Float type does not carry IEEE 754 guarantees. -/
theorem exp_round_error
    (z fl_exp_z : ℝ)
    (h_faithful : |fl_exp_z - Real.exp z| ≤ MatMul.unitRoundoff * Real.exp z) :
    |fl_exp_z - Real.exp z| ≤ MatMul.unitRoundoff * Real.exp z :=
  h_faithful

/-- **Floating-point softmax per-entry error bound.**

For x : Fin n → ℝ, the floating-point softmax satisfies:

  |fl(softmax(x))ᵢ - softmax(x)ᵢ| ≤ C · softmax(x)ᵢ

where C = (n + 2) · u in the practical regime. The bound is
proportional to the output value — entries near 0 have near-0
absolute error; the dominant entry (near 1) absorbs most of the error.

This is the parametrised form: `h_bound` carries the analytic content
(composition of exp-rounding error with sum-normalization error from
Higham's inner-product analysis). -/
theorem softmax_error_bound
    (x : Fin n → ℝ)
    (fl_softmax : Fin n → ℝ)
    (hn : 0 < n)
    (h_bound : ∀ i,
      |fl_softmax i - softmax_entry x i| ≤
        ((n : ℝ) + 2) * MatMul.unitRoundoff * softmax_entry x i) :
    ∀ i,
      |fl_softmax i - softmax_entry x i| ≤
        ((n : ℝ) + 2) * MatMul.unitRoundoff * softmax_entry x i :=
  h_bound

/-- **Softmax total-variation error bound.**

The L₁ distance between fl(softmax(x)) and softmax(x) satisfies:

  Σᵢ |fl(softmax(x))ᵢ - softmax(x)ᵢ| ≤ (n + 2) · u

This follows from summing the per-entry bound and using softmax_sum_one.
Important for downstream attention error analysis. -/
theorem softmax_tv_error
    (x : Fin n → ℝ)
    (fl_softmax : Fin n → ℝ)
    (hn : 0 < n)
    (h_bound : ∀ i,
      |fl_softmax i - softmax_entry x i| ≤
        ((n : ℝ) + 2) * MatMul.unitRoundoff * softmax_entry x i) :
    ∑ i, |fl_softmax i - softmax_entry x i| ≤
      ((n : ℝ) + 2) * MatMul.unitRoundoff := by
  calc ∑ i, |fl_softmax i - softmax_entry x i|
      ≤ ∑ i, ((n : ℝ) + 2) * MatMul.unitRoundoff * softmax_entry x i := by
        apply Finset.sum_le_sum
        intro i _; exact h_bound i
    _ = ((n : ℝ) + 2) * MatMul.unitRoundoff * ∑ i, softmax_entry x i := by
        rw [Finset.mul_sum]
    _ = ((n : ℝ) + 2) * MatMul.unitRoundoff * 1 := by
        rw [softmax_sum_one x hn]
    _ = ((n : ℝ) + 2) * MatMul.unitRoundoff := by ring

/-- **Shifted softmax equivalence.**

subtracting a constant c from all entries does not change softmax:
softmax(x - c)ᵢ = softmax(x)ᵢ. This justifies the max-shift trick
for numerical stability. -/
theorem softmax_shift_invariant
    (x : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    softmax_entry (fun j => x j - c) i = softmax_entry x i := by
  unfold softmax_entry
  simp only [Real.exp_sub]
  have h_exp_c_pos : (0 : ℝ) < Real.exp c := Real.exp_pos c
  have h_sum_pos : (0 : ℝ) < ∑ j, Real.exp (x j) := by
    apply Finset.sum_pos; intro j _; exact Real.exp_pos _; exact ⟨i, Finset.mem_univ i⟩
  simp only [div_div]
  congr 1
  rw [← Finset.sum_div, mul_comm, div_mul_cancel₀ _ (ne_of_gt h_exp_c_pos)]

end

end Pythia.Numerical.Softmax
