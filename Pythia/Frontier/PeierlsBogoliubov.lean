/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Peierls–Bogoliubov Inequality (Jensen form)

(1/d) ∑ᵢ exp(λᵢ) ≥ exp((1/d) ∑ᵢ λᵢ)

## Main results

* `trace_eigenvalues_eq` — ∑ eigenvalues = trace (for Hermitian matrices)
-/
import Mathlib
import Pythia.Frontier.MatrixLieb

open Finset BigOperators

noncomputable section

namespace Pythia.PeierlsBogoliubov

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem trace_eigenvalues_eq (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i : ℂ)) = A.trace :=
  hA.trace_eq_sum_eigenvalues.symm

end Pythia.PeierlsBogoliubov
