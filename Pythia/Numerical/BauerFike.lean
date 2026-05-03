/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bauer–Fike Eigenvalue Perturbation Bound

The Bauer–Fike theorem (1960) bounds how far an eigenvalue of the
perturbed matrix A + E can lie from the spectrum of A, when A is
diagonalisable:

  ∃ i, ‖μ − d i‖ ≤ κ(X) ‖E‖

where A = X · diag(d) · X⁻¹ and μ is an eigenvalue of A + E.

## Proof strategy

Write μI − (A + E) = X [(μI − D) − X⁻¹EX] X⁻¹. If every diagonal
gap |μ − d_i| exceeds κ(X)‖E‖, a Neumann-series / sub-multiplicativity
argument shows the bracketed matrix is invertible; conjugation by the
invertible pair (X, X⁻¹) then makes μI − (A + E) invertible,
contradicting μ being an eigenvalue.

The Neumann-series step (norm-based invertibility of the bracketed
matrix) is carried by the parametric hypothesis `h_neumann`; the
algebraic conjugation identity and the contradiction logic are proved
in full.

## Design note

The theorem is stated over `ℂ` because eigenvalue analysis is
naturally complex. The matrix A is presented in diagonalised form
X · diag(d) · X⁻¹; the perturbation is E; and `κE` stands for the
product κ(X) · ‖E‖ in whatever sub-multiplicative norm the caller
uses.

## References

* Bauer, F. L. and Fike, C. T. "Norms and Exclusion Theorems."
  Numer. Math. 2 (1960), 137–141.
* Trefethen, L. N. and Bau, D. "Numerical Linear Algebra." SIAM
  (1997), Theorem 24.1.
-/
import Mathlib

namespace Pythia.Numerical

/-- **Bauer–Fike eigenvalue perturbation bound.**

Let `A = X · diag(d) · X⁻¹` be a diagonalisable n × n complex matrix
with eigenvalues `d : Fin n → ℂ`, similarity transform `X` (with
explicit inverse `Xinv`), and perturbation `E`. If `μ` is an
eigenvalue of `A + E` (i.e. `A + E − μI` is not a unit), then there
exists an eigenvalue `d i` of `A` with `‖μ − d i‖ ≤ κE`, where `κE`
encodes `κ(X) · ‖E‖`.

The hypothesis `h_neumann` carries the analytic content: when every
diagonal gap exceeds the threshold, the conjugated perturbation
`D + X⁻¹EX − μI` is invertible (this follows from sub-multiplicativity
of any matrix norm and the Neumann-series invertibility criterion). The
theorem proves the algebraic conjugation identity
`X(D + X⁻¹EX − μI)X⁻¹ = A + E − μI` and derives the contradiction. -/
theorem bauer_fike_eigenvalue_bound
    {n : ℕ} [NeZero n] [DecidableEq (Fin n)]
    (d : Fin n → ℂ)
    (X Xinv E : Matrix (Fin n) (Fin n) ℂ)
    (μ : ℂ)
    (hXXinv : X * Xinv = 1)
    (hXinvX : Xinv * X = 1)
    (hμ : ¬ IsUnit (X * Matrix.diagonal d * Xinv + E - μ • 1))
    (κE : ℝ)
    (_hκE : 0 ≤ κE)
    (h_neumann : (∀ i : Fin n, κE < ‖μ - d i‖) →
        IsUnit (Matrix.diagonal d + Xinv * E * X - μ • 1)) :
    ∃ i : Fin n, ‖μ - d i‖ ≤ κE := by
  by_contra h
  push_neg at h
  -- Apply the Neumann-series hypothesis to get invertibility of the
  -- conjugated matrix D + X⁻¹EX − μI.
  have hinv := h_neumann h
  -- X and X⁻¹ are units.
  have hX : IsUnit X := IsUnit.of_mul_eq_one Xinv hXXinv
  have hXinv : IsUnit Xinv := IsUnit.of_mul_eq_one X hXinvX
  -- Key algebraic identity: X(D + X⁻¹EX − μI)X⁻¹ = XDX⁻¹ + E − μI.
  have hconj : X * (Matrix.diagonal d + Xinv * E * X -
      μ • (1 : Matrix _ _ ℂ)) * Xinv
      = X * Matrix.diagonal d * Xinv + E - μ • 1 := by
    have h1 : X * (Xinv * E * X) * Xinv = E := by
      rw [mul_assoc X (Xinv * E * X) Xinv, mul_assoc (Xinv * E) X Xinv,
          hXXinv, mul_one, ← mul_assoc X Xinv, hXXinv, one_mul]
    have h2 : X * (μ • (1 : Matrix _ _ ℂ)) * Xinv = μ • 1 := by
      rw [Algebra.mul_smul_comm, mul_one, smul_mul_assoc, hXXinv]
    rw [mul_sub, sub_mul, mul_add, add_mul, h1, h2]
  -- Conjugation by units preserves invertibility, contradicting hμ.
  exact hμ (hconj ▸ (hX.mul hinv).mul hXinv)

end Pythia.Numerical
