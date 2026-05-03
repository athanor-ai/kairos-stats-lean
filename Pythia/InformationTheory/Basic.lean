/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.Basic

Foundational results for the information-theory module: Shannon entropy
non-negativity at the PMF level. First brick in the InformationTheory
expansion (ATH-938) under the ATH-937 130-theorem roadmap.
-/

import Mathlib

namespace Pythia.InformationTheory

/-- **Shannon entropy of a finite-alphabet PMF is non-negative.**
The Shannon entropy `H(p) := ∑ a, -p(a) · log(p(a))` is non-negative for any
probability mass function `p` over a finite alphabet whose values are in [0,1].

Reference: Cover-Thomas, *Elements of Information Theory* (2nd ed.), §2.1. -/
theorem shannonEntropy_nonneg
    {α : Type*} [Fintype α]
    (p : α → ℝ)
    (h_nonneg : ∀ a, 0 ≤ p a)
    (h_le_one : ∀ a, p a ≤ 1) :
    0 ≤ ∑ a, Real.negMulLog (p a) := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (h_nonneg a) (h_le_one a)

end Pythia.InformationTheory
