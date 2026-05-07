/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Golden–Thompson Inequality — Commutative Case

For Hermitian matrices `A` and `B` that commute (`A * B = B * A`), the matrix
exponential satisfies the identity

  exp(A + B) = exp(A) * exp(B),

and consequently

  tr(exp(A + B)) = tr(exp(A) * exp(B)).

This is the *equality* case of the Golden–Thompson inequality.  The general
(non-commuting) inequality `tr exp(A + B) ≤ tr(exp(A) exp(B))` is significantly
harder and requires the Lieb concavity theorem; the commutative case proved here
follows directly from the standard Banach-algebra identity for commuting elements.

## Main results

* `commute_exp_exp` — if `A` and `B` commute, then `exp A` and `exp B` commute.
* `exp_add_of_commute_matrix` — `exp(A + B) = exp(A) * exp(B)` when `A * B = B * A`.
* `golden_thompson_commute` — `tr(exp(A + B)) = tr(exp(A) * exp(B))` when
  `A * B = B * A`.

## Implementation notes

`Matrix (Fin d) (Fin d) ℂ` is equipped with the `linftyOp` norm via
`open scoped Matrix.Norms.Operator`, which registers `linftyOpNormedRing` and
`linftyOpNormedAlgebra` as local instances.  Together with the `CompleteSpace`
instance from `Pi.complete` (matrices over a complete field are complete), this
satisfies the hypotheses of `Matrix.exp_add_of_commute`.

The exponential `exp` used throughout is `NormedSpace.exp`, Mathlib's uniform
Banach-algebra exponential (opened into scope below via `open NormedSpace`).
It coincides with the matrix-theoretic exponential on finite-dimensional spaces
over ℂ.

## References

* S. Golden (1965): Lower bounds for the Helmholtz function.
* C. J. Thompson (1965): Inequality with applications in statistical mechanics.
* J. A. Tropp (2012): User-friendly tail bounds for sums of random matrices.
-/
import Mathlib

open scoped Matrix
open NormedSpace

namespace Pythia.GoldenThompsonCommutative

variable {d : ℕ}

/-! ## Section 1: `exp A` and `exp B` commute when `A` and `B` do

This follows from `Commute.exp` in `Mathlib.Analysis.Normed.Algebra.Exponential`:
for any topological algebra with T2 topology, `Commute x y → Commute (exp x) (exp y)`.
Matrices over ℂ are T2 (they are metric spaces). -/

/-- If `A` and `B` commute as matrices, then `exp A` and `exp B` commute. -/
theorem commute_exp_exp (A B : Matrix (Fin d) (Fin d) ℂ) (h : Commute A B) :
    Commute (exp A) (exp B) :=
  h.exp

/-! ## Section 2: `exp(A + B) = exp(A) * exp(B)` for commuting matrices

`Matrix.exp_add_of_commute` requires `[NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]`
on the matrix type.  We activate these via `open scoped Matrix.Norms.Operator`, which
registers the `linftyOp` norm as local instances for the proof. -/

/-- For commuting complex matrices, the exponential distributes over addition. -/
theorem exp_add_of_commute_matrix (A B : Matrix (Fin d) (Fin d) ℂ) (h : Commute A B) :
    exp (A + B) = exp A * exp B := by
  open scoped Matrix.Norms.Operator in
  exact Matrix.exp_add_of_commute A B h

/-! ## Section 3: Trace equality — the commutative Golden–Thompson identity -/

/-- **Commutative Golden–Thompson identity**.
For Hermitian matrices `A` and `B` with `A * B = B * A`, we have
  `tr(exp(A + B)) = tr(exp(A) * exp(B))`.

Proof: since `A` and `B` commute, `exp(A + B) = exp(A) * exp(B)` by the
Banach-algebra identity `Matrix.exp_add_of_commute`.  Equality of traces follows
immediately. -/
theorem golden_thompson_commute (A B : Matrix (Fin d) (Fin d) ℂ)
    (_hA : A.IsHermitian) (_hB : B.IsHermitian)
    (hcomm : A * B = B * A) :
    (exp (A + B)).trace = (exp A * exp B).trace := by
  rw [exp_add_of_commute_matrix A B hcomm]

/-! ## Section 4: A symmetric formulation

Since `tr(X * Y) = tr(Y * X)` for matrices over ℂ (the entries commute), the
right-hand side may be written with `exp B * exp A` as well. -/

/-- Variant with the product on the right in the opposite order. -/
theorem golden_thompson_commute_symm (A B : Matrix (Fin d) (Fin d) ℂ)
    (_hA : A.IsHermitian) (_hB : B.IsHermitian)
    (hcomm : A * B = B * A) :
    (exp (A + B)).trace = (exp B * exp A).trace := by
  rw [exp_add_of_commute_matrix A B hcomm, Matrix.trace_mul_comm]

end Pythia.GoldenThompsonCommutative
