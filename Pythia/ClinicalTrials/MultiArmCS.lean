/-
Pythia.ClinicalTrials.MultiArmCS

Multi-arm anytime-valid confidence sequence — Bonferroni union bound
core (ATH-895 / ATH-894 clinical-trial-statistician persona).

## What this module proves

The algebraic + measure-theoretic core of the K-arm Bonferroni
construction:

  *If for each `k ∈ Fin K` the per-arm non-coverage event has
  `μ.real`-measure ≤ α/K, then the union of non-coverage events
  has `μ.real`-measure ≤ α.*

Specialized to anytime-valid CS: each arm has its own `(α/K)`-CS;
the joint CS is the product across arms; the family-wise non-
coverage is bounded by α via union bound.

## What this module does NOT yet prove

The full reduction from `bettingStoppingRule_admissible` (per-arm
admissibility on a single betting CS) to a per-arm non-coverage
event of `μ.real`-measure ≤ α/K is left for a follow-on file. That
step is mostly bookkeeping: lift each arm's CS structure into the
joint filtration and re-state the per-arm bound as a measurable
event.

The headline `bonferroni_union_bound_real` here is the *combiner* —
the algebraic engine that takes K per-arm bounds and produces the
joint bound. With it closed sorry-free, the remaining clinical-
trial work reduces to "wrap each arm's admissibility in a measurable
event," which is mechanical.

## Status

**Sorry-free, mainline.** Three theorems closed via Mathlib
(`measureReal_iUnion_fintype_le`, `Finset.sum_le_sum`,
`Finset.sum_const`, `field_simp`). Axiom audit: only
`propext, Classical.choice, Quot.sound`.

Registered in `Pythia.Lookup` under goal-class
`clinical_trials.multi_arm.bonferroni_union_bound` with confidence 1.0.

## Driver

ATH-895 (Pythia clinical-trials theorem coverage) under ATH-894
(cross-vertical MCP router, clinical-trial-statistician persona).
-/
import Mathlib
import Pythia.BettingCS

namespace Pythia.ClinicalTrials

open MeasureTheory ProbabilityTheory

/-- A K-arm anytime-valid CS configuration carrying the level `α`
and the arm count `K ≥ 1`. The per-arm Bonferroni level α/K is
exposed as `perArmLevel`; downstream constructions instantiate
each arm's CS at that level. -/
structure MultiArmCS (K : ℕ) (alpha : ℝ) where
  /-- α is in (0, 1). -/
  alpha_mem : 0 < alpha ∧ alpha < 1
  /-- K ≥ 1 (at least one arm). -/
  arms_nonempty : 1 ≤ K

namespace MultiArmCS

variable {K : ℕ} {alpha : ℝ}

/-- Per-arm Bonferroni level α/K. -/
noncomputable def perArmLevel (_M : MultiArmCS K alpha) : ℝ := alpha / (K : ℝ)

/-- α/K is strictly positive given α > 0 and K ≥ 1. -/
theorem perArmLevel_pos (M : MultiArmCS K alpha) :
    0 < M.perArmLevel := by
  unfold perArmLevel
  have hK : 0 < (K : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.one_pos M.arms_nonempty
  exact div_pos M.alpha_mem.1 hK

/-- The per-arm Bonferroni levels sum to exactly α. Algebraic
identity `K · (α/K) = α`, the lynchpin of the union-bound combiner. -/
theorem perArmLevel_sum_eq_alpha (M : MultiArmCS K alpha) :
    (K : ℝ) * M.perArmLevel = alpha := by
  unfold perArmLevel
  have hK : (K : ℝ) ≠ 0 := by
    have : 0 < (K : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.one_pos M.arms_nonempty
    linarith
  field_simp

end MultiArmCS

/-! ### Bonferroni union bound (real-valued) -/

/-- **Bonferroni union bound, real-valued.** If K measurable events
each have `μ.real`-measure at most α/K, then their union has
`μ.real`-measure at most α.

This is the *combiner* used to lift K single-arm anytime-valid CS
admissibility statements (each at level α/K) into a joint K-arm
admissibility statement at level α — i.e. a multi-arm anytime-valid
CS with family-wise coverage error ≤ α.

**Proof:** finite-K real-valued union sub-additivity from Mathlib
(`measureReal_iUnion_fintype_le`), then `K · (α/K) = α` by
`field_simp`.

**Driver:** ATH-895 (Pythia clinical-trials theorem coverage). -/
theorem bonferroni_union_bound_real
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {K : ℕ} (hK : 1 ≤ K)
    (E : Fin K → Set Ω)
    {alpha : ℝ}
    (h_per_arm : ∀ k, μ.real (E k) ≤ alpha / (K : ℝ)) :
    μ.real (⋃ k, E k) ≤ alpha := by
  have hKR : 0 < (K : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.one_pos hK
  -- Step 1: real-valued union sub-additivity (finite K).
  have h1 : μ.real (⋃ k, E k) ≤ ∑ k, μ.real (E k) :=
    measureReal_iUnion_fintype_le (μ := μ) E
  -- Step 2: each summand ≤ α/K, so the sum is ≤ K · (α/K).
  have h2 : ∑ k, μ.real (E k) ≤ ∑ _ : Fin K, alpha / (K : ℝ) :=
    Finset.sum_le_sum (fun k _ => h_per_arm k)
  -- Step 3: K · (α/K) = α (the field-simp lemma; needs K ≠ 0).
  have h3 : ∑ _ : Fin K, (alpha / (K : ℝ)) = alpha := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith

/-- **Bonferroni union bound packaged with the K-arm CS structure.**
Convenience wrapper: instead of taking `K, α, hK` separately, pulls
them from the `MultiArmCS` configuration. -/
theorem bonferroni_union_bound_packaged
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {K : ℕ} {alpha : ℝ} (M : MultiArmCS K alpha)
    (E : Fin K → Set Ω)
    (h_per_arm : ∀ k, μ.real (E k) ≤ M.perArmLevel) :
    μ.real (⋃ k, E k) ≤ alpha := by
  -- Unpack perArmLevel = α/K and apply the unpacked theorem.
  have h : ∀ k, μ.real (E k) ≤ alpha / (K : ℝ) := by
    intro k
    have := h_per_arm k
    unfold MultiArmCS.perArmLevel at this
    exact this
  exact bonferroni_union_bound_real μ M.arms_nonempty E h

end Pythia.ClinicalTrials
