/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trace Inequalities for Positive Semidefinite / Definite Matrices

This module proves trace inequalities for complex Hermitian matrices, working with
`Matrix (Fin d) (Fin d) ℂ`.  All results are sorry-free.  Theorems whose proofs require
infrastructure not yet in Mathlib v4.28.0 (e.g., the general Von Neumann trace
inequality, or the Gibbs variational principle) are omitted per the project policy
(skip rather than leave sorries).

## Main results

* `trace_re_nonneg_of_posSemidef` — tr(A).re ≥ 0 for PSD A.
* `trace_monotone` — A ⪰ B (Loewner order) ⟹ tr(B).re ≤ tr(A).re.
* `trace_sandwich_nonneg` — 0 ≤ tr(Cᴴ A C).re for PSD A.
* `trace_mul_re_nonneg_of_commuting_psd` — 0 ≤ tr(A B).re when A, B commuting PSD.
* `trace_conjTranspose_mul_self_nonneg` — 0 ≤ tr(Aᴴ A).re for any A.
* `trace_diag_mul_eq_inner` — tr(diag(a) · diag(b)).re = ∑ᵢ aᵢbᵢ.
* `trace_diag_mul_nonneg_of_nonneg` — nonneg diagonal PSD product trace.
* `trace_diag_mul_le_of_antitone` — rearrangement inequality (diagonal case).
* `trace_diag_mul_le_of_antitone'` — rearrangement inequality (second arg permuted).

## References

* R. Bhatia, *Matrix Analysis*, Springer 1997, Ch. IV.
* J. von Neumann, "Some matrix-inequalities and metrization of matrix-space",
  Tomsk. Univ. Rev. 1 (1937), 286–300.
-/
import Mathlib

open scoped Matrix ComplexOrder BigOperators MatrixOrder

noncomputable section

namespace Pythia.TraceInequalities

variable {d : ℕ}

/-! ## Section 1: Trace of PSD matrix has nonneg real part -/

/-- **Trace nonnegativity**: For `A : Matrix (Fin d) (Fin d) ℂ` positive semidefinite,
`0 ≤ A.trace.re`.

**Proof**: By the spectral theorem, `A.trace = ∑ᵢ (eigenvalues i : ℂ)` and each
`eigenvalues i ≥ 0` for PSD matrices.  Taking real parts gives the result. -/
theorem trace_re_nonneg_of_posSemidef
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re := by
  classical
  have htrace : A.trace = ∑ i, (hA.1.eigenvalues i : ℂ) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues hA.1
  rw [htrace, map_sum]
  exact Finset.sum_nonneg fun i _ => by simp [RCLike.ofReal_re, hA.eigenvalues_nonneg i]

/-! ## Section 2: Trace monotonicity (Loewner order) -/

/-- **Trace monotonicity**: If `(A − B).PosSemidef` (Loewner order `A ⪰ B`), then
`B.trace.re ≤ A.trace.re`.

**Proof**: `(A − B).trace.re ≥ 0` from nonnegativity, and `(A − B).trace = A.trace − B.trace`
by linearity of trace. -/
theorem trace_monotone
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hAB : (A - B).PosSemidef) :
    B.trace.re ≤ A.trace.re := by
  have h := trace_re_nonneg_of_posSemidef hAB
  have heq : (A - B).trace = A.trace - B.trace := Matrix.trace_sub A B
  rw [heq, Complex.sub_re] at h
  linarith

/-! ## Section 3: Trace of product of PSD matrices -/

/-- **Trace sandwich nonnegativity**: For PSD `A` and any `C : Matrix (Fin d) (Fin d) ℂ`,
`0 ≤ (Cᴴ * A * C).trace.re`.

**Proof**: `Cᴴ * A * C` is PSD (by the Hermitian sandwiching lemma), then apply
`trace_re_nonneg_of_posSemidef`. -/
theorem trace_sandwich_nonneg
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ (Cᴴ * A * C).trace.re :=
  trace_re_nonneg_of_posSemidef (Matrix.PosSemidef.conjTranspose_mul_mul_same hA C)

/-- **Trace of product of commuting PSD matrices**: If `A.PosSemidef`, `B.PosSemidef`
and `Commute A B`, then `0 ≤ (A * B).trace.re`.

**Proof**: In the Loewner-ordered C⋆-algebra of matrices, commuting nonneg elements
have nonneg product (`Commute.mul_nonneg`). -/
theorem trace_mul_re_nonneg_of_commuting_psd
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hcomm : Commute A B) :
    0 ≤ (A * B).trace.re :=
  trace_re_nonneg_of_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp
      (Commute.mul_nonneg hA.nonneg hB.nonneg hcomm))

/-- **Self-product trace nonnegativity**: For any `A : Matrix (Fin d) (Fin d) ℂ`,
`0 ≤ (Aᴴ * A).trace.re`. -/
theorem trace_conjTranspose_mul_self_nonneg
    (A : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ (Aᴴ * A).trace.re :=
  trace_re_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)

/-! ## Section 4: Diagonal trace inner product -/

/-- **Diagonal product trace identity**: For real sequences `a b : n → ℝ`,
`tr(diag(↑a) * diag(↑b)).re = ∑ᵢ a i * b i`.

Uses `diag(f) * diag(g) = diag(f * g)` and `tr(diag f) = ∑ᵢ f i`. -/
theorem trace_diag_mul_eq_inner {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℝ) :
    ((Matrix.diagonal ((↑) ∘ a) * Matrix.diagonal ((↑) ∘ b) : Matrix n n ℂ)).trace.re =
      ∑ i, a i * b i := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [Function.comp_apply, ← Complex.ofReal_mul]

/-- **Nonneg diagonal trace product**: If `a i ≥ 0` and `b i ≥ 0` for all `i`,
`tr(diag(↑a) * diag(↑b)).re ≥ 0`. -/
theorem trace_diag_mul_nonneg_of_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ ((Matrix.diagonal ((↑) ∘ a) * Matrix.diagonal ((↑) ∘ b) : Matrix n n ℂ)).trace.re := by
  rw [trace_diag_mul_eq_inner]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hb i)

/-! ## Section 5: Von Neumann trace inequality — diagonal case via rearrangement -/

/-- **Rearrangement inequality (permute first argument)**:
If `a : Fin d → ℝ` and `b : Fin d → ℝ` are both antitone, then for any
`σ : Equiv.Perm (Fin d)`,
`tr(diag(↑(a ∘ σ)) * diag(↑b)).re ≤ tr(diag(↑a) * diag(↑b)).re`.

Equivalently, `∑ᵢ a(σ i) * b i ≤ ∑ᵢ a i * b i`.

**Proof**: Two antitone functions monovary together (`Antitone.monovary`), and the
rearrangement inequality (`Monovary.sum_comp_perm_mul_le_sum_mul`) applies. -/
theorem trace_diag_mul_le_of_antitone {d : ℕ}
    (a b : Fin d → ℝ) (ha : Antitone a) (hb : Antitone b)
    (σ : Equiv.Perm (Fin d)) :
    ((Matrix.diagonal ((↑) ∘ (a ∘ σ)) * Matrix.diagonal ((↑) ∘ b) :
        Matrix (Fin d) (Fin d) ℂ)).trace.re ≤
    ((Matrix.diagonal ((↑) ∘ a) * Matrix.diagonal ((↑) ∘ b) :
        Matrix (Fin d) (Fin d) ℂ)).trace.re := by
  simp only [trace_diag_mul_eq_inner, Function.comp_apply]
  exact (ha.monovary hb).sum_comp_perm_mul_le_sum_mul σ

/-- **Rearrangement inequality (permute second argument)**:
If `a` and `b` are both antitone, `∑ᵢ a i * b(σ i) ≤ ∑ᵢ a i * b i`. -/
theorem trace_diag_mul_le_of_antitone' {d : ℕ}
    (a b : Fin d → ℝ) (ha : Antitone a) (hb : Antitone b)
    (σ : Equiv.Perm (Fin d)) :
    ((Matrix.diagonal ((↑) ∘ a) * Matrix.diagonal ((↑) ∘ (b ∘ σ)) :
        Matrix (Fin d) (Fin d) ℂ)).trace.re ≤
    ((Matrix.diagonal ((↑) ∘ a) * Matrix.diagonal ((↑) ∘ b) :
        Matrix (Fin d) (Fin d) ℂ)).trace.re := by
  simp only [trace_diag_mul_eq_inner, Function.comp_apply]
  exact (ha.monovary hb).sum_mul_comp_perm_le_sum_mul σ

/-! ## Section 6: Auxiliary scalar lemma (originally trace_diag_nonneg) -/

/-- **Scalar pointwise product nonnegativity**: For nonneg real sequences `a`, `b`,
`0 ≤ ∑ᵢ a i * b i`. -/
theorem sum_mul_nonneg_of_nonneg {n : Type*} [Fintype n]
    (a b : n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ ∑ i, a i * b i :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hb i)

end Pythia.TraceInequalities

end
