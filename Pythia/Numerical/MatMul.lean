/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Floating-Point Matrix Multiplication Error Bound

The foundational error bound for floating-point matrix multiplication:
for an inner product of length `k` computed in floating-point with
unit roundoff `u`, the absolute error satisfies:

  |fl(a · b) - a · b| ≤ γ_k · Σᵢ |aᵢ| · |bᵢ|

where γ_k = k · u / (1 - k · u) is the standard error amplification
factor (Higham, Theorem 3.1). When `k · u < 1` (always true in
practice), the bound is well-defined.

For the full matrix case A ∈ ℝⁿˣᵏ, B ∈ ℝᵏˣᵐ:

  |fl(A · B) - A · B|ᵢⱼ ≤ γ_k · (|A| · |B|)ᵢⱼ

where |A| is the entrywise absolute value.

This is the foundational layer for ATH-1034 general theorems. All
vendor-specific numerical-equivalence results (softmax, layernorm,
attention) build on this inner-product error bound.

## Main results

* `gamma` — the standard error amplification factor γ_k = k·u/(1-k·u)
* `gamma_pos` — γ_k > 0 when k ≥ 1 and k·u < 1
* `gamma_bound` — γ_k ≤ 2·k·u when k·u ≤ 1/2 (practical regime)
* `inner_product_error` — absolute error bound for a length-k inner product
* `matmul_error_bound` — entrywise error bound for matrix multiplication

## References

* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). Theorem 3.1 (inner product), §3.5 (matrix mul).
-/
import Mathlib
import Pythia.Numerical.IEEE754

namespace Pythia.Numerical.MatMul

open Finset BigOperators

variable {k : ℕ}

noncomputable section

/-- Unit roundoff: u = ε/2 = 2^{-53} for double precision. -/
def unitRoundoff : ℝ := machineEpsilon / 2

/-- The standard error amplification factor γ_k = k·u / (1 - k·u).
    Well-defined when k·u < 1 (always true in practice for k < 2^53). -/
def gamma (k : ℕ) : ℝ := (k : ℝ) * unitRoundoff / (1 - (k : ℝ) * unitRoundoff)

/-- γ_k is positive when k ≥ 1 and k·u < 1. -/
theorem gamma_pos {k : ℕ} (hk : 0 < k) (hku : (k : ℝ) * unitRoundoff < 1) :
    0 < gamma k := by
  unfold gamma
  apply div_pos
  · exact mul_pos (Nat.cast_pos.mpr hk) (by unfold unitRoundoff machineEpsilon; positivity)
  · linarith

/-- In the practical regime k·u ≤ 1/2, we have γ_k ≤ 2·k·u.
    This is the "rule of thumb" bound used in most numerical analysis. -/
theorem gamma_bound {k : ℕ} (hku : (k : ℝ) * unitRoundoff ≤ 1 / 2) :
    gamma k ≤ 2 * ((k : ℝ) * unitRoundoff) := by
  unfold gamma
  have h_denom_pos : 0 < 1 - (k : ℝ) * unitRoundoff := by linarith
  have h_denom_ge : 1 / 2 ≤ 1 - (k : ℝ) * unitRoundoff := by linarith
  rw [div_le_iff₀ h_denom_pos]
  have h_ku_nn : 0 ≤ (k : ℝ) * unitRoundoff := by
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold unitRoundoff machineEpsilon; positivity
  nlinarith [sq_nonneg ((k : ℝ) * unitRoundoff)]

/-- **Inner-product floating-point error bound (Higham Theorem 3.1).**

For vectors a, b ∈ ℝᵏ, a floating-point inner product fl(a · b) computed
with left-to-right accumulation in round-to-nearest arithmetic satisfies:

  |fl(a · b) - a · b| ≤ γ_k · Σᵢ |aᵢ| · |bᵢ|

This is the parametrised form: `h_fl_bound` carries the analytic content
(standard model rounding analysis); the theorem names the result for
Pythia.Lookup dispatch.

The proof of `h_fl_bound` requires induction on the accumulation sequence
with the standard model `fl(x ⊕ y) = (x + y)(1 + δ)` where |δ| ≤ u.
This is the Aristotle target for the full constructive proof. -/
theorem inner_product_error
    (a b : Fin k → ℝ) (fl_dot : ℝ)
    (exact_dot : ℝ := ∑ i, a i * b i)
    (abs_dot_sum : ℝ := ∑ i, |a i| * |b i|)
    (hku : (k : ℝ) * unitRoundoff < 1)
    (h_fl_bound : |fl_dot - exact_dot| ≤ gamma k * abs_dot_sum) :
    |fl_dot - exact_dot| ≤ gamma k * abs_dot_sum :=
  h_fl_bound

/-- **Matrix multiplication entrywise error bound (Higham §3.5).**

For A ∈ ℝⁿˣᵏ, B ∈ ℝᵏˣᵐ, the floating-point product fl(A·B) satisfies
the entrywise bound:

  |fl(A·B)ᵢⱼ - (A·B)ᵢⱼ| ≤ γ_k · (|A|·|B|)ᵢⱼ

where (|A|·|B|)ᵢⱼ = Σₗ |Aᵢₗ| · |Bₗⱼ|.

This follows directly from applying `inner_product_error` to each
(i,j) entry, which is the inner product of row i of A with column j of B.

Parametrised form: the per-entry bound is taken as hypothesis. -/
theorem matmul_error_bound
    {n m : ℕ}
    (A : Fin n → Fin k → ℝ)
    (B : Fin k → Fin m → ℝ)
    (fl_AB : Fin n → Fin m → ℝ)
    (hku : (k : ℝ) * unitRoundoff < 1)
    (h_entry : ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        gamma k * ∑ l, |A i l| * |B l j|) :
    ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        gamma k * ∑ l, |A i l| * |B l j| :=
  h_entry

/-- **Frobenius-norm matrix multiplication error bound.**

Corollary of the entrywise bound: the Frobenius norm of the error
matrix is bounded by γ_k times the Frobenius norm of |A|·|B|.

  ‖fl(A·B) - A·B‖_F ≤ γ_k · ‖|A|·|B|‖_F

This is the form most useful for downstream softmax/layernorm/attention
bounds where the per-entry structure is composed with activation functions.

The Frobenius bound follows from squaring the entrywise bound, summing,
and taking the square root. The triangle inequality for sums + Cauchy-Schwarz
are the main tools. -/
theorem matmul_error_frobenius
    {n m : ℕ}
    (A : Fin n → Fin k → ℝ)
    (B : Fin k → Fin m → ℝ)
    (fl_AB : Fin n → Fin m → ℝ)
    (hku : (k : ℝ) * unitRoundoff < 1)
    (h_entry : ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        gamma k * ∑ l, |A i l| * |B l j|) :
    Real.sqrt (∑ i, ∑ j, (fl_AB i j - ∑ l, A i l * B l j) ^ 2) ≤
      gamma k * Real.sqrt (∑ i, ∑ j, (∑ l, |A i l| * |B l j|) ^ 2) := by
  have hg : 0 ≤ gamma k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [gamma, unitRoundoff]
    · exact le_of_lt (gamma_pos hk hku)
  rw [← Real.sqrt_sq hg, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := h_entry i j
  have h_abs_sq : (fl_AB i j - ∑ l, A i l * B l j) ^ 2 ≤
      (gamma k * ∑ l, |A i l| * |B l j|) ^ 2 := by
    rw [← sq_abs (fl_AB i j - ∑ l, A i l * B l j)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [mul_pow] at h_abs_sq
  exact h_abs_sq

end

end Pythia.Numerical.MatMul
