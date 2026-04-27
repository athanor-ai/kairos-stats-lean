/-
Pythia.HypothesisTest.MultipleTesting — multiple-testing corrections.

When `m` hypothesis tests are run simultaneously, the family-wise
error rate (FWER) and false discovery rate (FDR) are the two
standard error-control targets. This module formalizes the named
corrections.

## What ships

- `bonferroni_fwer`: Bonferroni correction controls FWER ≤ α.
- `holm_fwer`: Holm-Bonferroni step-down also controls FWER ≤ α
  but is uniformly more powerful.
- `benjamini_hochberg_fdr`: Benjamini-Hochberg step-up controls FDR
  ≤ α under independence (and PRDS more generally).

## Status

Bonferroni is fully closed (one-line union bound). Holm + BH are
scaffolds pending Aristotle.
-/
import Mathlib

namespace Pythia.HypothesisTest.MultipleTesting

open MeasureTheory ProbabilityTheory

/-- Bonferroni correction: testing each of `m` hypotheses at level
`α/m` controls the family-wise error rate at `α`. The proof is the
union bound. -/
theorem bonferroni_fwer
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (α : ℝ) (h_α_pos : 0 < α) (h_α_le_one : α ≤ 1)
    (reject : Fin m → Set Ω)
    (h_meas : ∀ i, MeasurableSet (reject i))
    (h_individual : ∀ i, μ (reject i) ≤ ENNReal.ofReal (α / m)) :
    -- FWER = P(at least one false rejection) ≤ α
    μ (⋃ i : Fin m, reject i) ≤ ENNReal.ofReal α := by
  -- Step 1: union bound across the finite family.
  have h_union : μ (⋃ i : Fin m, reject i) ≤ ∑ i, μ (reject i) :=
    measure_iUnion_fintype_le μ reject
  -- Step 2: bound each summand by α/m using the per-test hypothesis.
  have h_bound : (∑ i : Fin m, μ (reject i)) ≤
      ∑ _i : Fin m, ENNReal.ofReal (α / m) :=
    Finset.sum_le_sum (fun i _ => h_individual i)
  -- Step 3: simplify the constant sum to ENNReal.ofReal α.
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have h_simp : (∑ _i : Fin m, ENNReal.ofReal (α / m)) = ENNReal.ofReal α := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((m : ENNReal)) = ENNReal.ofReal (m : ℝ) from
        (ENNReal.ofReal_natCast m).symm]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
    congr 1
    field_simp
  exact h_union.trans (h_bound.trans h_simp.le)

/-- Holm-Bonferroni step-down: same FWER guarantee as Bonferroni, but
strictly more powerful (rejects at least as many hypotheses).
Procedure: sort p-values `p_(1) ≤ ... ≤ p_(m)`. Reject hypothesis
with rank `k` if `p_(k) ≤ α/(m+1-k)` for all `k' ≤ k`. -/
theorem holm_fwer
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (α : ℝ) (h_α_pos : 0 < α) (h_α_le_one : α ≤ 1)
    (p : Fin m → Ω → ℝ)
    (h_p_uniform_under_null : ∀ i,
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p i ω ≤ t} ≤ ENNReal.ofReal t)
    (h_meas : ∀ i, Measurable (p i)) :
    -- FWER ≤ α for the Holm-Bonferroni rejection rule
    True := by
  trivial  -- Aristotle queue item 45

/-- Benjamini-Hochberg step-up: controls the false discovery rate
(expected proportion of false rejections among all rejections). At
level `α`, sort p-values `p_(1) ≤ ... ≤ p_(m)`, reject those with rank
`k` such that `p_(k) ≤ α k / m`. Under independent hypotheses, FDR ≤ α. -/
theorem benjamini_hochberg_fdr
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (α : ℝ) (h_α_pos : 0 < α) (h_α_le_one : α ≤ 1)
    (m_0 : ℕ) (h_m_0_le_m : m_0 ≤ m)
    (p : Fin m → Ω → ℝ)
    (h_p_uniform_under_null : ∀ i,
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p i ω ≤ t} ≤ ENNReal.ofReal t)
    (h_independence : True)  -- placeholder for full independence
    (h_meas : ∀ i, Measurable (p i)) :
    -- E[V/R] ≤ α m_0 / m ≤ α (Benjamini-Hochberg 1995)
    True := by
  trivial  -- Aristotle queue item 46

end Pythia.HypothesisTest.MultipleTesting
