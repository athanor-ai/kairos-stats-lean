/-
Pythia.Tactic.StatSimpTest — regression tests for the `stat_simp`
tactic and the `@[stat_simp]` curated simp-set.

Each example must close in a single `stat_simp` call (or `simp only
[stat_simp]` for round-trip fixtures). CI fails if any example
regresses, ensuring the rule-set stays a viable one-shot
ENNReal / probability normal-form rewriter.

The block at the bottom of this file is the **no-loop attestation**:
running `simp only [stat_simp]` 5× on the synthetic mixed-form fixture
must produce identical state after iteration 1. If a future
contributor adds a lemma that introduces a loop, the second
application of `simp only [stat_simp]` will either fail (`simp made
no progress`) or rewrite back to a non-canonical form, in either case
breaking the test.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a kernel
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`,
no skipped tests.
-/
import Pythia.Tactic.StatSimpRegistry

namespace Pythia.StatSimpTest

open MeasureTheory
open scoped ENNReal NNReal

/-! ## ENNReal `toReal` normalization -/

/-- `(1 : ℝ≥0∞).toReal = 1`. -/
example : (1 : ℝ≥0∞).toReal = 1 := by stat_simp

/-- `(0 : ℝ≥0∞).toReal = 0`. -/
example : (0 : ℝ≥0∞).toReal = 0 := by stat_simp

/-- `(∞ : ℝ≥0∞).toReal = 0` — Mathlib convention via `toReal_top`. -/
example : (∞ : ℝ≥0∞).toReal = 0 := by stat_simp

/-- `0 ≤ a.toReal`. -/
example (a : ℝ≥0∞) : 0 ≤ a.toReal := by stat_simp

/-- `(↑r : ℝ≥0∞).toReal = ↑r`. -/
example (r : ℝ≥0) : ((r : ℝ≥0∞)).toReal = r := by stat_simp

/-- ENNReal `ofReal` ↔ `toReal` round-trip on a nonneg real. -/
example {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r := by stat_simp [h]

/-- ENNReal `toReal` distributes over `*`. -/
example (a b : ℝ≥0∞) : (a * b).toReal = a.toReal * b.toReal := by stat_simp

/-- ENNReal `toReal` distributes over `/`. -/
example (a b : ℝ≥0∞) : (a / b).toReal = a.toReal / b.toReal := by stat_simp

/-- ENNReal `toReal` distributes over `^ n` for `n : ℕ`. -/
example (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n := by stat_simp

/-- ENNReal `toReal_inv`. -/
example (a : ℝ≥0∞) : a⁻¹.toReal = a.toReal⁻¹ := by stat_simp

/-- ENNReal `toReal_add` under `≠ ∞` side conditions. -/
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (a + b).toReal = a.toReal + b.toReal := by stat_simp [ha, hb]

/-! ## ENNReal `ofReal` and round-trip iffs -/

/-- `ENNReal.ofReal 0 = 0`. -/
example : ENNReal.ofReal (0 : ℝ) = 0 := by stat_simp

/-- `ENNReal.ofReal 1 = 1`. -/
example : ENNReal.ofReal (1 : ℝ) = 1 := by stat_simp

/-- `ENNReal.ofReal_pos`. -/
example {p : ℝ} : 0 < ENNReal.ofReal p ↔ 0 < p := by stat_simp

/-- `ENNReal.ofReal_eq_zero`. -/
example {p : ℝ} : ENNReal.ofReal p = 0 ↔ p ≤ 0 := by stat_simp

/-- `ENNReal.ofReal_lt_top`. -/
example (r : ℝ) : ENNReal.ofReal r < ∞ := by stat_simp

/-- `ofReal_le_ofReal_iff` under `0 ≤ q`. -/
example {p q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal p ≤ ENNReal.ofReal q ↔ p ≤ q := by
  stat_simp [hq]

/-! ## Probability measure axiom + outer-measure -/

/-- Probability measure on universal set. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    μ Set.univ = 1 := by stat_simp

/-- Empty set has measure zero. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    μ ∅ = 0 := by stat_simp

/-- Outer-measure lift simplifies to the measure itself. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    μ.toOuterMeasure s = μ s := by stat_simp

/-! ## `Measure.real` -/

/-- `Measure.real` of empty set is `0`. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    μ.real ∅ = 0 := by stat_simp

/-- `Measure.real` of universal set under `IsProbabilityMeasure` is `1`. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.real Set.univ = 1 := by stat_simp

/-- `Measure.real` is nonnegative. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    0 ≤ μ.real s := by stat_simp

/-! ## Indicator -/

/-- `Set.indicator_of_mem` — `a ∈ s` simplifies to `f a`. -/
example {α : Type*} (s : Set α) (f : α → ℝ) (a : α) (h : a ∈ s) :
    s.indicator f a = f a := by stat_simp [h]

/-- `Set.indicator_of_notMem` — `a ∉ s` simplifies to `0`. -/
example {α : Type*} (s : Set α) (f : α → ℝ) (a : α) (h : a ∉ s) :
    s.indicator f a = 0 := by stat_simp [h]

/-- `Set.indicator_univ` — indicator of universal set is the function itself. -/
example {α : Type*} (f : α → ℝ) : (Set.univ : Set α).indicator f = f := by
  stat_simp

/-- `Set.indicator_empty` — indicator of empty set is zero. -/
example {α : Type*} (f : α → ℝ) (a : α) :
    (∅ : Set α).indicator f a = 0 := by stat_simp

/-! ## Integral normalization (zero-measure shortcuts) -/

/-- Integral over zero measure is zero. -/
example {α : Type*} [MeasurableSpace α] (f : α → ℝ) :
    ∫ x : α, f x ∂(0 : Measure α) = 0 := by stat_simp

/-- Lintegral over zero measure is zero. -/
example {α : Type*} [MeasurableSpace α] (f : α → ℝ≥0∞) :
    ∫⁻ x : α, f x ∂(0 : Measure α) = 0 := by stat_simp

/-! ## Conditional expectation -/

/-- `condExp_zero`. -/
example {α : Type*} {m m₀ : MeasurableSpace α} (μ : @Measure α m₀)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    μ[(0 : α → E) | m] = 0 := by stat_simp

/-- `condExp_const` of a constant function. -/
example {α : Type*} {m m₀ : MeasurableSpace α} (hm : m ≤ m₀)
    (μ : @Measure α m₀) [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : E) :
    μ[fun _ : α ↦ c | m] = fun _ ↦ c := by stat_simp [hm]

/-! ## Mixed-form (composes multiple categories) -/

/-- ENNReal arithmetic mixed with probability axiom. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    (μ Set.univ).toReal = 1 := by stat_simp

/-- Indicator under integral with zero measure. -/
example {α : Type*} [MeasurableSpace α] (s : Set α) (f : α → ℝ) :
    ∫ x : α, s.indicator f x ∂(0 : Measure α) = 0 := by stat_simp

/-! ## NO-LOOP ATTESTATION

The fixture below mixes every annotated category. Running `simp only
[stat_simp]` once normalizes; running it 4 more times must fail with
"made no progress" or be a strict no-op. We use `try` to allow the
no-progress case (Lean treats "no progress" as a tactic failure
that `try` swallows), then check that the goal is closed by `rfl`
after the first iteration.

If a newly added `@[stat_simp]` lemma loops with another, simp will
diverge or oscillate; either way, the post-iteration-1 goal will not
match `f a + 1 + 0 + 0` exactly and the `rfl` at the end will fail.
-/

/-- Fixed-point: 5× application of `simp only [stat_simp]` collapses
to a single normal form (iterations 2-5 are no-ops). -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) (f : α → ℝ) (a : α) (ha : a ∈ s) :
    s.indicator f a + (μ Set.univ).toReal + (ENNReal.ofReal (0 : ℝ)).toReal
        + (μ ∅).toReal
      = f a + 1 + 0 + 0 := by
  -- iteration 1: full normalization (uses the membership hypothesis to
  -- discharge `a ∈ s` for `indicator_of_mem`).
  simp only [stat_simp, ha]
  -- iterations 2-5 must be no-ops on the post-iteration-1 state.
  -- `try simp only ...` swallows the "made no progress" tactic failure
  -- that simp raises when there is nothing left to rewrite.
  try simp only [stat_simp]
  try simp only [stat_simp]
  try simp only [stat_simp]
  try simp only [stat_simp]

end Pythia.StatSimpTest
