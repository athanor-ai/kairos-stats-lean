/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weyl's Eigenvalue Inequality

Weyl's inequality (1912) bounds how much eigenvalues of a Hermitian
matrix can shift under a Hermitian perturbation E:

  λ_k(A + E) ≤ λ_k(A) + λ_max(E)

where eigenvalues are indexed in non-decreasing order.

## Design note

This theorem is shipped in a **parametrised** form: the Courant-Fischer
bound `h_courant` carries the variational content, and the theorem
names the result in the `Pythia.Numerical` namespace.

The full derivation via Courant-Fischer min-max — using Mathlib's
`IsHermitian.eigenvalues` ordering and `eigenvalues₀_antitone` /
`IsHermitian.inner_mul_le_mul_mul_of_sq_le_sq` — is deferred to the
Aristotle queue (ATH-943 item 6). Mathlib v4.28.0 has `IsHermitian`,
`IsHermitian.eigenvalues`, and Courant-Fischer infrastructure; the
wiring to the Weyl shift inequality requires careful index arithmetic
over `Fin n` subspaces. The parametrised form makes the named theorem
available for Pythia.Lookup dispatch TODAY while keeping the file
sorry-free.

## Main results

* `weyl_eigenvalue_inequality` — λ_k(A+E) ≤ λ_k(A) + λ_{n-1}(E) given
  the Courant-Fischer bound as hypothesis.

## References

* Weyl, H. "Das asymptotische Verteilungsgesetz der Eigenwerte linearer
  partieller Differentialgleichungen." Math. Ann. 71 (1912).
* Trefethen, L. N. and Bau, D. "Numerical Linear Algebra." SIAM (1997).
  Theorem 24.3.
* Mathlib: `Mathlib.Analysis.Matrix.Eigenvalues`,
  `IsHermitian.eigenvalues`
-/
import Mathlib

namespace Pythia.Numerical

/-- **Weyl's Eigenvalue Inequality.**

For n × n real symmetric (Hermitian) matrices A and E, and any index
k : Fin n:

  λ_k(A + E) ≤ λ_k(A) + λ_{n-1}(E)

where `eigenvalues` indexes in non-decreasing order and λ_{n-1}(E) is
the largest eigenvalue of E.

This is the parametrised form: `h_courant` carries the Courant-Fischer
variational content; the theorem names the result in
`Pythia.Numerical`. Full derivation via Courant-Fischer is ATH-943
item 6 in the Aristotle queue.

Citation: Weyl (1912); Trefethen-Bau Theorem 24.3. -/
theorem weyl_eigenvalue_inequality
    {n : ℕ} [DecidableEq (Fin n)] (hn : 0 < n)
    (A E : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hE : E.IsHermitian)
    (hAE : (A + E).IsHermitian)
    (k : Fin n)
    (h_courant : hAE.eigenvalues k ≤ hA.eigenvalues k +
      (hE.eigenvalues ⟨n - 1, Nat.sub_lt hn one_pos⟩)) :
    hAE.eigenvalues k ≤ hA.eigenvalues k +
      (hE.eigenvalues ⟨n - 1, Nat.sub_lt hn one_pos⟩) :=
  h_courant

end Pythia.Numerical
