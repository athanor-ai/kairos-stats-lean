/-
Pythia.Tactic.StatsIneq — the `stats_ineq` tactic.

A domain inequality hammer for the pythia library, modeled on
Mathlib's `bound` tactic. Where `pythia` is the general-purpose
"close any stats goal" hammer (aesop-driven), `stats_ineq` specialises
to monotonicity / nonnegativity / subadditivity inequalities common
in concentration-of-measure proofs:

  • `√x ≤ √y` when `x ≤ y`
  • `0 ≤ log x` when `1 ≤ x`
  • `etaBetting b ≤ etaHR b` when `1 ≤ b`
  • `0 ≤ a + b` when `0 ≤ a, 0 ≤ b`

## Architecture

* `@[stats_ineq]` user attribute. Two effects:
  1. Re-elaborates as `@[bound]` so Mathlib's mature bound dispatch
     picks the lemma up automatically.
  2. Records the declaration name in `statsIneqExt` for `#stats_ineqs`
     introspection.

* `stats_ineq` tactic. Tries (in order):
  1. `bound` — the Mathlib hammer with the pythia-tagged rule set.
  2. `positivity` — nonnegativity goals.
  3. `gcongr` — generalised-congruence monotonicity goals.
  4. `linarith` — linear arithmetic close-out.
  5. `nlinarith` — nonlinear arithmetic close-out.

* `#stats_ineqs` command — list every registered `@[stats_ineq]`
  lemma in scope.

## Lean-gating

Every `example` in `StatsIneqTest.lean` reduces to a Lean kernel-checked
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
skipped tests. Per Aidan's 2026-04-25 directive.

## Driver

Pythia headline tactic shipped in `Tactic/Pythia.lean`; this
is the cleanest pythia extension per the Mathlib-tactic-surface
analysis.
-/
import Mathlib
import Pythia.Quantization
import Pythia.MatchingConstants

namespace Pythia

open Lean Elab Meta Tactic

/-- Environment extension storing the names of all `@[stats_ineq]`-tagged
declarations. Surfaced via `#stats_ineqs`. -/
initialize statsIneqExt :
    SimpleScopedEnvExtension Name (Std.HashSet Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := ∅
  }

/-- `@[stats_ineq]` — register a theorem as a pythia inequality
rule. The lemma is forwarded to Mathlib's `@[bound]` attribute, so the
underlying `bound` tactic (and therefore `stats_ineq`) picks it up
automatically. The declaration name is also recorded in `statsIneqExt`
for `#stats_ineqs`. -/
initialize registerBuiltinAttribute {
  name := `stats_ineq
  descr := "Register theorem as a pythia `@[bound]` rule for the `stats_ineq` tactic."
  add := fun decl _stx kind => do
    -- Forward to Mathlib's `@[bound]`. If the lemma is already in the
    -- bound ruleset (e.g. the upstream Mathlib tagging), swallow the
    -- duplicate-registration error: the scoped extension below still
    -- records the name, which is what `#stats_ineqs` cares about.
    let boundStx ← `(attr| bound)
    try
      Attribute.add decl `bound boundStx kind
    catch _ => pure ()
    statsIneqExt.add decl
}

/-- `stats_ineq` — pythia inequality hammer.

Tries Mathlib's `bound` tactic first (which dispatches via every
`@[bound]`-tagged lemma, including those we re-tagged with
`@[stats_ineq]`). On failure, falls through to `positivity`, `gcongr`,
`linarith`, `nlinarith` in that order. Designed for monotonicity,
nonnegativity, and subadditivity goals over ℝ that arise in
concentration / CS-rate proofs. -/
syntax (name := statsIneqTac) "stats_ineq" : tactic

@[tactic statsIneqTac] def evalStatsIneq : Tactic := fun stx => do
  match stx with
  | `(tactic| stats_ineq) =>
    evalTactic <| ← `(tactic|
      first
        | bound
        | positivity
        | gcongr
        | linarith
        | nlinarith)
  | _ => throwUnsupportedSyntax

/-- `#stats_ineqs` — list every theorem tagged `@[stats_ineq]` in the
current scope. -/
elab "#stats_ineqs" : command => do
  let env ← getEnv
  let s := statsIneqExt.getState env
  if s.isEmpty then
    logInfo "no stats inequalities registered (use @[stats_ineq] to register one)"
  else
    let names := s.toList
    let lines := names.map (fun n => m!"  • {n}")
    logInfo (m!"registered stats inequalities ({names.length}):" ++ MessageData.joinSep lines "\n")

end Pythia
