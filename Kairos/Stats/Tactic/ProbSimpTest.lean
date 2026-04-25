/-
Kairos.Stats.Tactic.ProbSimpTest — regression tests for the
`prob_simp` / `pdf_simp` tactic.

Each example must close in a single `prob_simp` (or `pdf_simp`) call.
CI fails if any example regresses, ensuring the tactic stays viable as
a one-shot probability-normalization hammer.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a kernel
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`,
no skipped tests.
-/
import Kairos.Stats.Tactic.ProbSimpRegistry

namespace Kairos.Stats.ProbSimpTest

open MeasureTheory
open scoped ENNReal NNReal

/-- Probability measure on universal set. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    μ Set.univ = 1 := by prob_simp

/-- Probability measure on universal set, alias `pdf_simp`. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    μ Set.univ = 1 := by pdf_simp

/-- Empty set has measure zero. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    μ ∅ = 0 := by prob_simp

/-- Lintegral of `1` against a probability measure equals 1. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    ∫⁻ _, (1 : ℝ≥0∞) ∂μ = 1 := by prob_simp

/-- Outer-measure lift simplifies to the measure itself. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    μ.toOuterMeasure s = μ s := by prob_simp

/-- ENNReal `(1:ℝ≥0∞).toReal = 1`. -/
example : (1 : ℝ≥0∞).toReal = 1 := by prob_simp

/-- ENNReal `(0:ℝ≥0∞).toReal = 0`. -/
example : (0 : ℝ≥0∞).toReal = 0 := by prob_simp

/-- ENNReal `ofReal` ↔ `toReal` round-trip on a nonneg real. -/
example {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r := by prob_simp

/-- ENNReal `ofReal_one`. -/
example : ENNReal.ofReal (1 : ℝ) = 1 := by prob_simp

/-- ENNReal `ofReal_zero`. -/
example : ENNReal.ofReal (0 : ℝ) = 0 := by prob_simp

/-- Integral of constant against zero measure. -/
example {α : Type*} [MeasurableSpace α] (c : ℝ) :
    ∫ _ : α, c ∂(0 : Measure α) = 0 := by prob_simp

/-- Integral of constant `c` against probability measure equals `c`. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c : ℝ) : ∫ _ : α, c ∂μ = c := by prob_simp

end Kairos.Stats.ProbSimpTest

-- The `#prob_simps` command surfaces the registered rule set.
#prob_simps
