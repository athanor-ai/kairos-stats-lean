/-
examples/02_anytime_valid_smoke.lean — the `anytime_valid` tactic.

The Phase B marquee tactic. Two variants:

* *Countable-time* (no args): the infinite-horizon Ville bound.
* *Finite-horizon* (`(horizon := N)`): bounded sup over t ≤ N.
-/
import Pythia.Tactic.AnytimeValid

open Pythia MeasureTheory

namespace Pythia.Examples.AnytimeValid

example
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c}
      ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid

example
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    μ {ω : Ω | ∃ t : ℕ, t ≤ N ∧ c ≤ f t ω}
      ≤ ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c) := by
  anytime_valid (horizon := N)

end Pythia.Examples.AnytimeValid
