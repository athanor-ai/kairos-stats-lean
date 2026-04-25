/-
Kairos.Stats.Tactic.AnytimeValidTest — sanity tests for the
`anytime_valid` tactic.

Each `example` is a regression test: it must compile. If the tactic
breaks, CI fails here before the broken implementation ever lands on
main. This file is the analogue of `MathlibTest/positivity.lean` for
our marquee tactic.
-/
import Kairos.Stats.Tactic.AnytimeValid

namespace Kairos.Stats.Tactic.Test

open MeasureTheory ProbabilityTheory ENNReal

/-- Test 1. Marquee form: countable-time Ville bound. The tactic
should close the goal given the four standard hypotheses in scope. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid

/-- Test 2. Same goal with hypotheses in reverse order. The tactic
must succeed regardless of the order in which hypotheses appear in
the local context. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    {c : ℝ} (hc : 0 < c)
    (hint : Integrable (f 0) μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hsup : Supermartingale f 𝓕 μ) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid

/-- Test 3. Finite-horizon variant: `anytime_valid (horizon := N)` closes
the finite-horizon Ville bound via `ville_supermartingale_finite`.
Requires `[IsProbabilityMeasure μ]`; no `Integrable` hypothesis needed. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    μ {ω : Ω | ∃ t : ℕ, t ≤ N ∧ c ≤ f t ω} ≤
      ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c) := by
  anytime_valid (horizon := N)

/-- Test 4. Explicit-witness variant: `anytime_valid using myMart` passes
the supermartingale term directly. `myMart` is a non-standard name;
the test exercises the `using` syntax rather than `assumption` lookup. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (myMart : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid using myMart

end Kairos.Stats.Tactic.Test
