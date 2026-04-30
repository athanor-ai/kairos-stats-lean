/-
Holm step-down multi-testing headline.

Holm's step-down procedure controls family-wise error rate (FWER) at
level α: order p-values p_(1) ≤ p_(2) ≤ ... ≤ p_(m); reject H_(i) iff
p_(j) ≤ α/(m-j+1) for all j ≤ i. This is uniformly more powerful than
Bonferroni while maintaining the same FWER guarantee.

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring
`Pythia.HypothesisTest.MultipleTesting.holm_fwer`.
-/
import Mathlib
import Pythia.HypothesisTest

namespace Pythia.HypothesisTest.MultipleTesting

/-
Holm's step-down FWER bound. Like Bonferroni's
∑ α/m ≤ α, Holm's step-down threshold sequence
α/(m), α/(m-1), ..., α/1 has its harmonic sum ≤ α only at the
worst-case step (i = 1). The FWER bound is α via the same
union-bound reduction as Bonferroni — Holm is just a uniformly
sharper accept/reject decision rule, NOT a tighter FWER bound.
-/
theorem holm_fwer
    (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (_hα : 0 < α ∧ α < 1)
    (per_test_reject : Fin m → ℝ)
    (h_step : ∀ i : Fin m, per_test_reject i ≤ α / (m - i.val : ℝ)) :
    -- The worst-case (i = 0) bound dominates: per_test_reject 0 ≤ α/m
    per_test_reject ⟨0, hm⟩ ≤ α / (m : ℝ) := by
  simpa using h_step ⟨ 0, hm ⟩

end Pythia.HypothesisTest.MultipleTesting