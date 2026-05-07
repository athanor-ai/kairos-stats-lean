/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-Sum-Exp Scalar Inequalities

## Main results

* `sum_exp_pos` — ∑ exp(xᵢ) > 0
* `log_sum_exp_ge_single` — log(∑ exp(xᵢ)) ≥ xⱼ
-/
import Mathlib

open Finset BigOperators

noncomputable section

namespace Pythia.LogSumExp

variable {n : Type*} [Fintype n] [Nonempty n]

theorem sum_exp_pos (f : n → ℝ) : 0 < ∑ i, Real.exp (f i) :=
  Finset.sum_pos (fun i _ => Real.exp_pos (f i)) ⟨Classical.arbitrary n, Finset.mem_univ _⟩

theorem log_sum_exp_ge_single (f : n → ℝ) (j : n) :
    Real.log (∑ i, Real.exp (f i)) ≥ f j := by
  rw [ge_iff_le, ← Real.exp_le_exp, Real.exp_log (sum_exp_pos f)]
  exact Finset.single_le_sum (fun i _ => le_of_lt (Real.exp_pos (f i))) (Finset.mem_univ j)

end Pythia.LogSumExp
