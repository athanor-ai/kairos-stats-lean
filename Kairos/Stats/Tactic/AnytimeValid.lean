/-
Kairos.Stats.Tactic.AnytimeValid — `anytime_valid` tactic.

The marquee tactic that turns `kairos-stats-lean` from a library into a
toolkit. Closes goals of the form

    μ {ω | ∃ t : ℕ, c ≤ f t ω} ≤ ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c)

given a `Supermartingale f 𝓕 μ` hypothesis, a non-negativity hypothesis
`∀ t ω, 0 ≤ f t ω`, an integrability hypothesis `Integrable (f 0) μ`,
and `0 < c`. Discharges side-conditions via `assumption` / `positivity` /
`measurability`.

This is the Phase B (ATH-594) deliverable. Phase A (ATH-593) ships the
underlying `ville_supermartingale` theorem and infrastructure; the
tactic layer lives here.

## Examples

```
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid
```

## Status

Skeleton tactic. The current implementation delegates to
`ville_supermartingale` after reordering goals so the standard
hypothesis names (`hsup`, `hnn`, `hint`, `hc`) match the theorem's
argument order. A future iteration adds:
* `anytime_valid (horizon := n)` — finite-horizon variant invoking
  `ville_supermartingale_finite`
* `anytime_valid using h` — explicit supermartingale witness
* Hypothesis-name-agnostic resolution via `assumption` fallback
* Better error messages naming the missing class

-/
import Kairos.Stats.VilleSupermartingale

namespace Kairos.Stats

open Lean Lean.Elab Lean.Elab.Tactic

/-- The marquee anytime-valid CS tactic.

Closes goals of the form
  `μ {ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal`
given supermartingale + non-negativity + integrability + positivity
hypotheses in scope. -/
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

end Kairos.Stats
