/-
Kairos.Stats.BernsteinTest — worked examples + regression tests for
`Kairos.Stats.bernstein_of_subGamma` and the surrounding Bernstein
family.

Lean-gating rule (Aidan 2026-04-25): every example here closes to a
kernel term against `{propext, Classical.choice, Quot.sound}`. No
`sorry`, no fake closures, no skipped tests.

The point of this file is to lock the dispatch surface for `pythia`:
- Example 1 instantiates `bernstein_of_subGamma` directly with
  `exact …`. Verifies the named lemma is callable from outside.
- Example 2 invokes `bernstein_of_subGamma` via `apply` from a goal
  with the Bernstein-rate shape. Verifies the API ergonomics.
- Example 3 closes the same goal via `pythia`. Verifies the
  `@[stat_lemma]` registration: pythia must dispatch to
  `bernstein_of_subGamma` automatically.

If example 3 ever breaks, the `@[stat_lemma]` integration with the
`pythia` aesop ruleset has regressed and the headline tactic no longer
covers Bernstein — block release.
-/
import Kairos.Stats.Bernstein

namespace Kairos.Stats.BernsteinTest

open Kairos.Stats MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Example 1 — direct call

Bernstein-shaped tail bound for a sub-gamma martingale, invoked
explicitly. The most common use site: a downstream author who has
already constructed a `SubGammaMG (V/N) (b/3) 𝓕 μ` instance from
their bounded-increment martingale. -/
example
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {V b : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (M : SubGammaMG (V / N) (b / 3) 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * (V + b * τ / 3)))) :=
  bernstein_of_subGamma hN M hM0 hτ

/-! ## Example 2 — `apply` ergonomics

The same goal closed via `apply`. Verifies that the explicit-argument
order matches what a user would naturally write at the tactic prompt. -/
example
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {V b : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (M : SubGammaMG (V / N) (b / 3) 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * (V + b * τ / 3)))) := by
  apply bernstein_of_subGamma hN M hM0 hτ

/-! ## Example 3 — `pythia` dispatch (CRITICAL)

The same goal closed via the headline `pythia` tactic. This is the
acceptance test for the `@[stat_lemma]` registration: `pythia` must
locate `bernstein_of_subGamma` in the `Kairos.Stats` aesop ruleset
and apply it without a manual hint.

If this regresses, the Bernstein lemma is invisible to the hammer —
which means downstream library code that previously closed in a
single `pythia` call would suddenly require a manual `apply`. This
is a release-blocking regression. -/
example
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {V b : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (M : SubGammaMG (V / N) (b / 3) 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * (V + b * τ / 3)))) := by
  pythia

end Kairos.Stats.BernsteinTest
