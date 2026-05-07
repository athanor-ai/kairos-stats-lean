/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trace Inequalities for PSD Matrices

## Main results

* `trace_re_nonneg_of_posSemidef` — tr(A).re ≥ 0 for PSD A
* `trace_monotone` — A ⪰ B ⟹ tr(B).re ≤ tr(A).re
* `trace_sandwich_nonneg` — 0 ≤ tr(Cᴴ A C).re for PSD A
* `trace_conjTranspose_mul_self_nonneg` — 0 ≤ tr(Aᴴ A).re
-/
import Mathlib

open scoped Matrix ComplexOrder BigOperators MatrixOrder

noncomputable section

namespace Pythia.TraceInequalities

variable {d : ℕ}

theorem trace_re_nonneg_of_posSemidef
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re := by
  classical
  have htrace : A.trace = ∑ i, (hA.1.eigenvalues i : ℂ) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues hA.1
  have : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    rw [htrace]; push_cast; simp [map_sum]
  rw [this]
  exact Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i

theorem trace_monotone
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hAB : (A - B).PosSemidef) :
    B.trace.re ≤ A.trace.re := by
  have h := trace_re_nonneg_of_posSemidef hAB
  simp only [Matrix.trace_sub, Complex.sub_re] at h
  linarith

theorem trace_sandwich_nonneg
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ (Cᴴ * A * C).trace.re :=
  trace_re_nonneg_of_posSemidef (Matrix.PosSemidef.conjTranspose_mul_mul_same hA C)

theorem trace_conjTranspose_mul_self_nonneg
    (A : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ (Aᴴ * A).trace.re :=
  trace_re_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)

end Pythia.TraceInequalities

end
