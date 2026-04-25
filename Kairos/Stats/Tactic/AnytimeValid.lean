/-
Kairos.Stats.Tactic.AnytimeValid — `anytime_valid` tactic.

The marquee tactic that turns `kairos-stats-lean` from a library into a
toolkit. Two variants:

**Countable-time** (no args):

    μ {ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal

given `Supermartingale f 𝓕 μ`, `∀ t ω, 0 ≤ f t ω`, `Integrable (f 0) μ`,
and `0 < c`. Requires `[IsFiniteMeasure μ]`.

**Finite-horizon** (`(horizon := N)`):

    μ {ω | ∃ t : ℕ, t ≤ N ∧ c ≤ f t ω} ≤ ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c)

given `Supermartingale f 𝓕 μ`, `∀ t ω, 0 ≤ f t ω`, and `0 < c`.
Requires `[IsProbabilityMeasure μ]`. No `Integrable` hypothesis needed.

**Explicit-witness** (`using h`):

    anytime_valid using myMart

Passes the `Supermartingale` term directly; side-conditions resolved via
`assumption`.

Side-conditions discharged via `assumption`.

This is the Phase B (ATH-594) deliverable. Phase A (ATH-593) ships the
underlying theorems; the tactic layer lives here.

## Examples

```
-- Countable-time variant
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid

-- Finite-horizon variant
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    μ {ω : Ω | ∃ t : ℕ, t ≤ N ∧ c ≤ f t ω} ≤
      ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c) := by
  anytime_valid (horizon := N)

-- Explicit-witness variant
example ... (myMart : Supermartingale f 𝓕 μ) ... := by
  anytime_valid using myMart
```

-/
import Kairos.Stats.VilleSupermartingale
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open Lean Lean.Elab Lean.Elab.Tactic

/-- The marquee anytime-valid CS tactic (countable-time variant).

Closes goals of the form
  `μ {ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal`
given supermartingale + non-negativity + integrability + positivity
hypotheses in scope. Requires `[IsFiniteMeasure μ]`. -/
syntax (name := anytimeValid) "anytime_valid" : tactic

elab_rules : tactic
  | `(tactic| anytime_valid) => do
    -- First pass: try to apply ville_supermartingale and close side-conditions
    -- via assumption. If that fails, surface the residual goals to the user.
    evalTactic <| ← `(tactic|
      first
        | (exact ville_supermartingale (by assumption) (by assumption)
            (by assumption) (by assumption))
        | (refine ville_supermartingale ?_ ?_ ?_ ?_ <;> assumption)
        | fail "anytime_valid: could not close goal. Required hypotheses in scope:\n  • Supermartingale f 𝓕 μ\n  • ∀ t ω, 0 ≤ f t ω\n  • Integrable (f 0) μ\n  • 0 < c\nGoal must be of the form: μ {ω | ∃ t, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal")

/-- The finite-horizon anytime-valid CS tactic.

Closes goals of the form
  `μ {ω | ∃ t : ℕ, t ≤ N ∧ c ≤ f t ω} ≤ ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c)`
given supermartingale + non-negativity + positivity hypotheses in scope.
Requires `[IsProbabilityMeasure μ]`. No `Integrable` hypothesis needed. -/
syntax (name := anytimeValidHorizon) "anytime_valid" " (" "horizon" " := " term ")" : tactic

elab_rules : tactic
  | `(tactic| anytime_valid (horizon := $n)) => do
    evalTactic <| ← `(tactic|
      first
        | (exact ville_supermartingale_finite (by assumption) (by assumption)
            (by assumption) $n)
        | (refine ville_supermartingale_finite ?_ ?_ ?_ $n <;> assumption)
        | fail "anytime_valid (horizon := N): could not close goal. Required hypotheses in scope:\n  • Supermartingale f 𝓕 μ\n  • ∀ t ω, 0 ≤ f t ω\n  • 0 < c\nGoal must be of the form: μ {ω | ∃ t, t ≤ N ∧ c ≤ f t ω} ≤ ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c). Requires [IsProbabilityMeasure μ].")

/-- Explicit-witness variant: `anytime_valid using h` lets the user supply
the supermartingale term directly instead of relying on `assumption`.

Useful when the hypothesis is named non-standardly, comes from a
lambda-bound term, or is constructed on the fly. Side-conditions
`∀ t ω, 0 ≤ f t ω`, `Integrable (f 0) μ`, and `0 < c` are still
resolved from the local context via `assumption`. -/
syntax (name := anytimeValidUsing) "anytime_valid" " using " term : tactic

elab_rules : tactic
  | `(tactic| anytime_valid using $h) => do
    evalTactic <| ← `(tactic|
      first
        | (exact ville_supermartingale $h (by assumption) (by assumption) (by assumption))
        | (refine ville_supermartingale $h ?_ ?_ ?_ <;> assumption)
        | fail "anytime_valid using h: could not close goal with the supplied supermartingale witness. Other side-conditions (∀ t ω, 0 ≤ f t ω, Integrable (f 0) μ, 0 < c) must still be in scope.")

end Kairos.Stats
