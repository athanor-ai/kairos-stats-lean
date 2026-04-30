/-
Stratified anytime-valid confidence sequence headline.

Extends Pythia.ClinicalTrials.MultiArmCS to within-stratum
martingale composition: if each stratum has its own (α/S)-anytime-
valid CS, the joint CS across S strata has coverage error ≤ α.

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring
`Pythia.ClinicalTrials.Stratified.stratified_admissible`.
-/
import Mathlib

-- import Pythia.ClinicalTrials.MultiArmCS -- removed: module not available in this project

namespace Pythia.ClinicalTrials.Stratified

open MeasureTheory ProbabilityTheory

/-- Stratified anytime-valid CS via Bonferroni union bound across strata.
If S strata each have a per-stratum non-coverage event of measure
≤ α/S, the joint non-coverage event has measure ≤ α. -/
theorem stratified_admissible
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : ℕ} (hS : 1 ≤ S)
    (E : Fin S → Set Ω)
    {α : ℝ}
    (h_per_stratum : ∀ s, μ.real (E s) ≤ α / (S : ℝ)) :
    μ.real (⋃ s, E s) ≤ α := by
  -- Use the union bound `measureReal_iUnion_fintype_le` to get `μ.real (⋃ s, E s) ≤ ∑ s, μ.real (E s)`.
  have h_union_bound : μ.real (⋃ s, E s) ≤ ∑ s, μ.real (E s) := by
    exact measureReal_iUnion_fintype_le E
  refine' le_trans h_union_bound (le_trans (Finset.sum_le_sum fun _ _ => h_per_stratum _) _)
  simp +decide [mul_div_cancel₀, show S ≠ 0 by linarith]

end Pythia.ClinicalTrials.Stratified