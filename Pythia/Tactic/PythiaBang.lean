/-
Pythia.Tactic.PythiaBang — `pythia!!` hammer ladder orchestrator.

The headline one-call closer for the pythia library. Where `pythia`
goes through a shape-dispatch cascade, `pythia!!` runs the FULL
ladder of available closers in priority order, fail-fast, first-to-
close-wins. Verbose variant `pythia!?` reports the closing rung and
per-rung timing.

## Ladder

  1. `stat_simp` (the dedicated `@[stat_simp]` simp set from ATH-754)
     with fall-through to core `simp`
  2. `linarith` / `nlinarith` / `polyrith` (numeric arithmetic)
  3. `positivity` (non-negativity goals)
  4. `aesop` on the registered `Pythia` ruleset
  5. `pythia` (existing shape-dispatch tactic; the @[stat_lemma]
     cascade lives behind it)
  6. `z3_check` (QF_LRA over ℝ)
  7. `cvc5_check` (QF_BV / QF_LRA backup)
  8. `vampire_check` / `e_check` (FOL oracles)
  9. `disprove` (counterexample finder; useful to catch vacuous
     statements — fails the proof attempt with a witness)

Each rung gets a per-rung budget (default 500ms via heartbeats); on
failure or timeout the next rung is tried. `pythia!?` records the
elapsed wall-clock per rung and emits a single info summary at the
end so the user can see which rung paid off and what the others cost.

## Offline-first / no LLM coupling

Pythia is an offline-first kernel-clean library (CONTRIBUTING rule 4).
The `pythia!!` ladder contains zero LLM rungs. The deterministic
external oracles on rungs 6-9 (`z3_check`, `cvc5_check`,
`vampire_check`, `e_check`) are SMT / ATP solvers with verifiable
Lean reconstruction, NOT language models. LLM-augmented closure
(DSPv2, Aristotle, etc.) lives in the kairos-sdk companion under
`kairos.lean_cycle.cycle_prove` and never reaches into this library.

## ATH-753 — research/ath-753-pythia-bang.
-/
import Pythia.Tactic.Pythia
import Pythia.Tactic.StatSimp
import Pythia.Tactic.Z3Check
import Pythia.Tactic.CVC5Check
import Pythia.Tactic.VampireCheck
import Pythia.Tactic.ECheck
import Pythia.Tactic.Disprove

namespace Pythia

open Lean Elab Meta Tactic

/-- Default per-rung budget for `pythia!!` rungs, expressed in
heartbeats. 200_000 heartbeats is roughly Lean's default ~2s budget;
we run each rung at ~500ms ≈ 50_000 heartbeats so a full ladder still
fits in a few seconds even when many rungs miss. -/
def pythiaBangDefaultHeartbeats : Nat := 50000

/-- Trace class for `pythia!?` verbose timing output. -/
initialize registerTraceClass `Pythia.Bang

/-- A single rung in the `pythia!!` ladder.

* `id`        — short machine-friendly identifier (e.g. `"simp"`).
* `descr`     — human-readable one-liner used in the verbose summary.
* `body`      — the tactic syntax to evaluate; must end with `done`
                so a partial close does not commit the rung.
-/
structure Rung where
  id    : String
  descr : String
  body  : TSyntax `tactic

/-- Build the canonical 9-rung ladder. Rung order matches the spec
in the module docstring; cheap fail-fast rungs go first.

The ladder is deliberately LLM-free per CONTRIBUTING rule 4
(offline-first, no LLM coupling). LLM-augmented closure lives in the
kairos-sdk companion (`kairos.lean_cycle.cycle_prove`), not here. -/
def buildRungs : MetaM (Array Rung) := do
  let r1 : TSyntax `tactic ← `(tactic|
    first
      | (stat_simp; done)
      | (simp; done))
  let r2 : TSyntax `tactic ← `(tactic|
    first
      | (linarith; done)
      | (nlinarith; done)
      | (polyrith; done))
  let r3 : TSyntax `tactic ← `(tactic| (positivity; done))
  let r4 : TSyntax `tactic ← `(tactic|
    (aesop (config := { warnOnNonterminal := false })
           (rule_sets := [Pythia]); done))
  let r5 : TSyntax `tactic ← `(tactic| (pythia; done))
  let r6 : TSyntax `tactic ← `(tactic| (z3_check; done))
  let r7 : TSyntax `tactic ← `(tactic| (cvc5_check; done))
  let r8 : TSyntax `tactic ← `(tactic|
    first
      | (vampire_check; done)
      | (e_check; done))
  let r9 : TSyntax `tactic ← `(tactic| (disprove; done))
  return #[
    ⟨"simp",            "@[stat_simp] (ATH-754) + core simp closure",     r1⟩,
    ⟨"linarith_chain",  "linarith / nlinarith / polyrith arithmetic",     r2⟩,
    ⟨"positivity",      "positivity (non-negativity goals)",              r3⟩,
    ⟨"aesop_pythia",    "aesop on the @[stat_lemma] Pythia ruleset",      r4⟩,
    ⟨"pythia",          "pythia shape-dispatch cascade",                  r5⟩,
    ⟨"z3_check",        "z3_check (QF_LRA over ℝ)",                       r6⟩,
    ⟨"cvc5_check",      "cvc5_check (QF_BV / QF_LRA backup)",             r7⟩,
    ⟨"fol_check",       "vampire_check / e_check (FOL oracles)",          r8⟩,
    ⟨"disprove",        "disprove (counterexample finder)",               r9⟩
  ]

/-- Try a single rung. Returns `some elapsedMs` on success and
`none` on failure (regardless of whether the failure was a tactic
exception, a heartbeat timeout, or a budget exhaustion). The rung
runs inside `withMaxHeartbeats budget` so a runaway tactic cannot
stall the whole ladder. -/
def tryRung (rung : Rung) (budget : Nat) : TacticM (Option Nat) := do
  let saved ← saveState
  let t0 ← IO.monoMsNow
  try
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget * 1000 }) do
      evalTactic rung.body
    let t1 ← IO.monoMsNow
    return some (t1 - t0)
  catch _ =>
    saved.restore
    return none

/-- `pythia!!` — fire the full hammer ladder; first rung to close wins. -/
syntax (name := pythiaBang) "pythia!!" : tactic

/-- `pythia!?` — verbose `pythia!!`. Logs the closing rung plus
per-rung timing for every rung tried. -/
syntax (name := pythiaBangVerbose) "pythia!?" : tactic

@[tactic pythiaBang] def evalPythiaBang : Tactic := fun stx => do
  match stx with
  | `(tactic| pythia!!) =>
    let rungs ← liftMetaM buildRungs
    let mut closed := false
    for rung in rungs do
      if closed then break
      match ← tryRung rung pythiaBangDefaultHeartbeats with
      | some _ =>
        closed := true
      | none =>
        pure ()
    unless closed do
      throwError "pythia!!: no rung closed the goal."
  | _ => throwUnsupportedSyntax

@[tactic pythiaBangVerbose] def evalPythiaBangVerbose : Tactic := fun stx => do
  match stx with
  | `(tactic| pythia!?) =>
    let rungs ← liftMetaM buildRungs
    let mut closed := false
    let mut summary : Array String := #[]
    let mut closingRung : Option String := none
    for rung in rungs do
      if closed then
        summary := summary.push s!"  {rung.id}: skipped (already closed)"
      else
        match ← tryRung rung pythiaBangDefaultHeartbeats with
        | some ms =>
          summary := summary.push s!"  {rung.id}: CLOSED in {ms}ms — {rung.descr}"
          closed := true
          closingRung := some rung.id
        | none =>
          summary := summary.push s!"  {rung.id}: failed — {rung.descr}"
    let body := String.intercalate "\n" summary.toList
    match closingRung with
    | some r =>
      logInfo m!"pythia!? — closed by `{r}`. Ladder timing:\n{body}"
    | none =>
      logInfo m!"pythia!? — no rung closed. Ladder timing:\n{body}"
      throwError "pythia!?: no rung closed the goal."
  | _ => throwUnsupportedSyntax

end Pythia
