/-
Pythia.Tactic.AnytimeValid — `anytime_valid` tactic.

The marquee anytime-valid CS hammer. Turns `pythia` from a
library of theorems into a usable toolkit. Closes goals of the form

  `μ {ω | ∃ t, M t ω ≥ a} ≤ <bound>`

by dispatching against a registered library of CS-family admissibility
lemmas (the `Pythia.AnytimeValid` aesop ruleset, populated by
`@[anytime_valid_lemma]`) and falling through to Ville's inequality on
sub-Gaussian / supermartingale processes.

## Variants

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

## Architecture

* `Pythia.AnytimeValid` aesop ruleset — declared at module load.
  Every `@[anytime_valid_lemma]`-tagged theorem joins it.

* `@[anytime_valid_lemma]` attribute — forwards to
  `@[aesop safe apply (rule_sets := [Pythia.AnytimeValid])]`. The
  declaration name is also recorded in `anytimeValidLemmaExt` for
  `#anytime_valid_lemmas` introspection.

* `anytime_valid` tactic — dispatch ladder:
  1. aesop against `[Pythia.AnytimeValid]` (registered admissibility
     lemmas, including `hrStoppingRule_admissible`,
     `bettingStoppingRule_admissible`, the Ville family, etc.).
  2. direct `ville_supermartingale` exact / refine path (legacy
     iteration-1 behaviour, kept for goal-shapes whose hypotheses match
     by `assumption` but whose conclusion shape doesn't unify under
     aesop's `safe apply`).
  3. error message naming the required hypotheses.

* `#anytime_valid_lemmas` command — list the registered library.

## Driver

Phase B v0.2.0 (countable-time + finite-horizon + using).
Phase B v0.3.0 (this iteration): registry + aesop dispatch.
-/
import Pythia.VilleSupermartingale
import Pythia.SubGaussianMG
import Aesop

/-! ## Registry: aesop ruleset + `@[anytime_valid_lemma]` attribute

The `Pythia.AnytimeValid` aesop ruleset. Every
`@[anytime_valid_lemma]`-tagged theorem joins this set. The
`anytime_valid` tactic queries it as the first stage of its dispatch
ladder. Declared at the top level (Aesop's `declare_aesop_rule_sets`
syntax category does not parse inside a `namespace` block). -/
declare_aesop_rule_sets [Pythia.AnytimeValid]

namespace Pythia

open Lean Lean.Elab Lean.Elab.Tactic

/-- Environment extension storing the names of all
`@[anytime_valid_lemma]`-tagged declarations. Surfaced via
`#anytime_valid_lemmas`. -/
initialize anytimeValidLemmaExt :
    SimpleScopedEnvExtension Name (Std.HashSet Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := ∅
  }

/-- `@[anytime_valid_lemma]` — register a theorem as an admissibility /
Ville-style closer for the `anytime_valid` tactic.

Internally this is shorthand for
`@[aesop safe apply (rule_sets := [Pythia.AnytimeValid])]`. The
declaration name is also recorded in `anytimeValidLemmaExt` for
`#anytime_valid_lemmas`.

Use this on user-facing CS admissibility theorems and Ville-style
inequalities so they auto-join the `anytime_valid` hammer.

```
@[anytime_valid_lemma]
theorem my_admissibility : ... := ...
```
-/
initialize registerBuiltinAttribute {
  name := `anytime_valid_lemma
  descr := "Register theorem as a pythia anytime-valid closer (`@[aesop safe apply (rule_sets := [Pythia.AnytimeValid])]`) for the `anytime_valid` tactic."
  add := fun decl _stx kind => do
    -- Forward to aesop. If the lemma is already in the ruleset, swallow
    -- the duplicate-registration error: the scoped extension still
    -- records the name.
    let aesopStx ← `(attr| aesop safe apply (rule_sets := [Pythia.AnytimeValid]))
    try
      Attribute.add decl `aesop aesopStx kind
    catch _ => pure ()
    anytimeValidLemmaExt.add decl
}

/-! ## Tactic syntax + dispatch -/

/-- The marquee anytime-valid CS tactic (countable-time variant).

Dispatch ladder (in order):
  1. aesop against the `Pythia.AnytimeValid` ruleset (registered
     `@[anytime_valid_lemma]` rules).
  2. `ville_supermartingale` exact/refine path with `assumption` for
     side-conditions.
  3. Error message naming the expected hypotheses.

Required hypotheses for the Ville fall-through:
  • `Supermartingale f 𝓕 μ`
  • `∀ t ω, 0 ≤ f t ω`
  • `Integrable (f 0) μ`
  • `0 < c`
Requires `[IsFiniteMeasure μ]`. -/
syntax (name := anytimeValid) "anytime_valid" : tactic

elab_rules : tactic
  | `(tactic| anytime_valid) => do
    evalTactic <| ← `(tactic|
      first
        | (exact ville_supermartingale (by assumption) (by assumption)
            (by assumption) (by assumption))
        | (refine ville_supermartingale ?_ ?_ ?_ ?_ <;> assumption)
        | (exact ville_supermartingale_unit_initial (by assumption) (by assumption)
            (by assumption) (by assumption))
        | (exact ville_supermartingale_infinite (by assumption) (by assumption)
            (by assumption))
        | (exact ville_ineq (by assumption) _ (by assumption) _ (by assumption)
            (by assumption))
        | aesop (config := { warnOnNonterminal := false })
                (rule_sets := [Pythia.AnytimeValid])
        | fail "anytime_valid: could not close goal. Either:\n  • register a closing lemma with @[anytime_valid_lemma], or\n  • have the Ville hypotheses in scope:\n      Supermartingale f 𝓕 μ\n      ∀ t ω, 0 ≤ f t ω\n      Integrable (f 0) μ\n      0 < c\n    with goal:\n      μ {ω | ∃ t, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal")

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

/-! ## Introspection -/

/-- `#anytime_valid_lemmas` — list every theorem tagged
`@[anytime_valid_lemma]` in the current scope. -/
elab "#anytime_valid_lemmas" : command => do
  let env ← getEnv
  let s := anytimeValidLemmaExt.getState env
  if s.isEmpty then
    logInfo "no anytime-valid lemmas registered (use @[anytime_valid_lemma] to register one)"
  else
    let names := s.toList
    let lines := names.map (fun n => m!"  • {n}")
    logInfo (m!"registered anytime-valid lemmas ({names.length}):" ++ MessageData.joinSep lines "\n")

end Pythia
