/-
Group-sequential SPRT (GSPRT) headline.

Extends Pythia.SPRT to a group-sequential design with K analyses
at sample sizes n_1 < n_2 < ... < n_K. Use Bonferroni splitting:
each analysis tested at level α/K, total type-I error ≤ α.

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring `Pythia.SPRT.GSPRT.gsprt_type_I`
that proves the type-I error bound.
-/
import Mathlib

namespace Pythia.SPRT.GSPRT

/-
Group-sequential SPRT type-I error bound. With K planned
analyses each at Bonferroni-adjusted level α/K, the joint type-I
error rate over all K analyses is at most α.
-/
theorem gsprt_type_I
    (K : ℕ) (hK : 1 ≤ K) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (typeI_per_analysis : Fin K → ℝ)
    (hTI : ∀ k, typeI_per_analysis k ≤ α / (K : ℝ)) :
    (∑ k, typeI_per_analysis k) ≤ α := by
  exact le_trans ( Finset.sum_le_sum fun _ _ => hTI _ ) ( by norm_num [ mul_div_cancel₀, show K ≠ 0 by linarith ] )

end Pythia.SPRT.GSPRT