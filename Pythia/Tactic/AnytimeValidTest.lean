/-
Pythia.Tactic.AnytimeValidTest — sanity tests for the
`anytime_valid` tactic.

Each `example` is a regression test: it must compile. If the tactic
breaks, CI fails here before the broken implementation ever lands on
main. This file is the analogue of `MathlibTest/positivity.lean` for
our marquee tactic.

## Coverage

Tests 1–4: legacy variants (countable-time, hypothesis-order
permutation, finite-horizon `(horizon := N)`, explicit-witness
`using h`). Exercise the Ville fall-through path.

Tests 5–7: registry-dispatch path. Exercise the
`Pythia.AnytimeValid` aesop ruleset populated by
`@[anytime_valid_lemma]` tags from `AnytimeValidRegistry.lean`.

## Lean-gating

No `sorry`, no `axiom`, no skipped tests. Per Aidan's 2026-04-25
directive: every example reduces to a kernel-checked term against
`{propext, Classical.choice, Quot.sound}`.
-/
import Pythia.Tactic.AnytimeValid
import Pythia.Tactic.AnytimeValidRegistry

namespace Pythia.Tactic.Test

open MeasureTheory ProbabilityTheory ENNReal Pythia

/-- Test 1. Marquee form: countable-time Ville bound. The tactic
should close the goal given the four standard hypotheses in scope.
Exercises the `ville_supermartingale` exact path. -/
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

/-- Test 5. Registry-dispatch path: infinite-horizon Ville on a
non-negative supermartingale over a probability measure. The
underlying lemma is `ville_supermartingale_infinite`, registered via
`@[anytime_valid_lemma]` in `AnytimeValidRegistry.lean`. The tactic
reaches it through the aesop ruleset rather than the legacy direct-
exact path. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    (hY : Supermartingale Y 𝓕 μ) (hY_nn : ∀ t ω, 0 ≤ Y t ω)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, c ≤ Y t ω} ≤
      ENNReal.ofReal ((∫ ω, Y 0 ω ∂μ) / c) := by
  anytime_valid

/-- Test 6. Registry-dispatch path: Ville bound for a sub-Gaussian
martingale (general σ), finite horizon, starting at 0 a.s. Exercises
`ville_ineq` from the registry on a goal whose conclusion mentions
the explicit Chernoff exponent `exp(-τ²/(2σ²N))`. The goal's RHS is
written in the exact form the lemma produces so unification succeeds
under aesop's `safe apply`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG σ 𝓕 μ) (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ ^ 2) / (2 * σ ^ 2 * N))) := by
  anytime_valid

/-- Test 7. Registry-dispatch path: unit-initial Ville bound. The
tactic finds `ville_supermartingale_unit_initial` via the
`anytime_valid` ladder's direct `refine` step (the registry-aware
fall-through that comes after the generic `ville_supermartingale`
attempt and before the aesop ruleset). -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnonneg : ∀ t ω, 0 ≤ f t ω)
    (hunit : ∀ᵐ ω ∂μ, f 0 ω = 1) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (1 / c).toNNReal := by
  anytime_valid

end Pythia.Tactic.Test

-- The `#anytime_valid_lemmas` command surfaces the registered library.
#anytime_valid_lemmas
