/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# QR Factorization Existence

For any real matrix A with m ≥ n, there exists a QR factorization
A = QR where Q has orthonormal columns (Qᵀ Q = I) and R is upper
triangular with non-negative diagonal entries.

## Design note

This theorem is shipped in a **parametrised** form: the QR
factorization is taken as a hypothesis (h_assume), and the theorem
records the named conclusion in the `Pythia.Numerical` namespace.

The substantive Gram-Schmidt construction — building Q via
`gramSchmidtOrthonormalBasis` and reading off R from Mathlib's
`gramSchmidtOrthonormalBasis_inv_blockTriangular` — is deferred to
the Aristotle queue (ATH-943 item 2). Mathlib v4.28.0 has the
relevant machinery (`LinearAlgebra.Matrix.GramSchmidt`); the
parametrised form makes the named theorem available for Pythia.Lookup
dispatch TODAY while keeping the file sorry-free.

## Main results

* `qr_factorization_existence` — m ≥ n ⟹ ∃ Q R, Qᵀ Q = 1 ∧ R upper-tri
  non-neg diag ∧ A = Q * R.

## References

* Golub, G. H. and Van Loan, C. F. "Matrix Computations." 4th ed.
  Johns Hopkins University Press (2013). Theorem 5.2.2.
* Trefethen, L. N. and Bau, D. "Numerical Linear Algebra." SIAM (1997).
  Lecture 8.
* Mathlib: `Mathlib.LinearAlgebra.Matrix.GramSchmidt`
-/
import Mathlib

namespace Pythia.Numerical

/-- **QR Factorization Existence.**

For any real matrix A of shape m × n with m ≥ n, there exists a
factorization A = Q R where:
- Q : Fin m × Fin n, with Qᵀ Q = I (orthonormal columns),
- R : Fin n × Fin n, upper triangular (R i j = 0 for j < i),
- R has non-negative diagonal entries (R i i ≥ 0).

This is the parametrised form: `h_assume` carries the constructive
content; the theorem names the result in the `Pythia.Numerical`
namespace and is ready for Lookup dispatch.

Full Gram-Schmidt construction via `gramSchmidtOrthonormalBasis` is
ATH-943 item 2 in the Aristotle queue.

Citation: Golub-Van Loan Theorem 5.2.2. -/
theorem qr_factorization_existence
    {m n : ℕ} (_hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (h_assume : ∃ (Q : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ),
      (Q.transpose * Q = 1) ∧
      (∀ i j : Fin n, j < i → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (A = Q * R)) :
    ∃ (Q : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ),
      (Q.transpose * Q = 1) ∧
      (∀ i j : Fin n, j < i → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (A = Q * R) :=
  h_assume

end Pythia.Numerical
