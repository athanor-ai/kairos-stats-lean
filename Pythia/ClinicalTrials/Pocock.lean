/-
Pocock alpha-spending boundary headline.

In a K-stage group-sequential design with equal alpha-spending,
the Pocock boundary uses a constant critical value c_K such that
the cumulative type-I error reaches exactly α at the K-th analysis.

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring `Pythia.ClinicalTrials.Pocock.boundary_alpha`.
-/
import Mathlib

namespace Pythia.ClinicalTrials.Pocock

/-
Pocock equal-alpha-spending boundary. With K stages and per-stage
crossing probability bounded by α/K, the cumulative type-I error
across all stages is at most α. This is the Bonferroni reduction
of the Pocock design — tighter constants come from the multivariate
normal recursion but the union-bound version is the safe baseline.
-/
theorem boundary_alpha
    (K : ℕ) (hK : 1 ≤ K) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (per_stage_cross : Fin K → ℝ)
    (hps : ∀ k, per_stage_cross k ≤ α / (K : ℝ)) :
    (∑ k, per_stage_cross k) ≤ α := by
  exact le_trans ( Finset.sum_le_sum fun _ _ => hps _ ) ( by norm_num [ mul_div_cancel₀, show K ≠ 0 by positivity ] )

end Pythia.ClinicalTrials.Pocock