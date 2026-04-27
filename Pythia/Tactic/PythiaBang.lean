/-
Pythia.Tactic.PythiaBang — `pythia!` hammer ladder orchestrator.

The headline one-call closer for the pythia library. Where `pythia`
goes through a shape-dispatch cascade, `pythia!` runs the FULL
ladder of available closers in priority order, fail-fast, first-to-
close-wins. Verbose variant `pythia?` reports the closing rung and
per-rung timing.

## Naming (ATH-756)

The tactic was originally introduced as `pythia!!` (two bangs) in
ATH-753 / PR #48. Renamed to `pythia!` in ATH-756 / PR #51 to match
the Lean idiom `simp!` / `field_simp!`. The verbose form moved from
`pythia!?` to `pythia?` to match `apply?` / `rw?` / `simp?` (the `?`
suffix universally means "show me what you did"). The legacy spelling
`pythia!!` survives as a deprecated alias for one minor version.

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
failure or timeout the next rung is tried. `pythia?` records the
elapsed wall-clock per rung and emits a single info summary at the
end so the user can see which rung paid off and what the others cost.

## Offline-first / no LLM coupling

Pythia is an offline-first kernel-clean library (CONTRIBUTING rule 4).
The `pythia!` ladder contains zero LLM rungs. The deterministic
external oracles on rungs 6-9 (`z3_check`, `cvc5_check`,
`vampire_check`, `e_check`) are SMT / ATP solvers with verifiable
Lean reconstruction, NOT language models. LLM-augmented closure
(DSPv2, Aristotle, etc.) lives in the kairos-sdk companion under
`kairos.lean_cycle.cycle_prove` and never reaches into this library.

## ATH-753 / ATH-756 / ATH-758.
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

/-- Default per-rung budget for `pythia!` rungs, expressed in
heartbeats. 200_000 heartbeats is roughly Lean's default ~2s budget;
we run each rung at ~500ms ≈ 50_000 heartbeats so a full ladder still
fits in a few seconds even when many rungs miss. -/
def pythiaBangDefaultHeartbeats : Nat := 50000

/-- Trace class for `pythia?` verbose timing output. -/
initialize registerTraceClass `Pythia.Bang

/-- `pythia.bang.machineFormat` — when true, `pythia?` emits a tagged
log line `[pythia.bang.result] {"rung": ..., "ms": ...}` (success) or
`[pythia.bang.failure] {"reason": ...}` (failure) in addition to the
human-readable summary. Mirrors the legacy `pythia.machineFormat`
option that fed the verbose plain-`pythia?` tactic before ATH-756.

Off by default to keep interactive `pythia?` output clean. Toggle via
`set_option pythia.bang.machineFormat true in pythia?` for a single
invocation, or globally via `set_option pythia.bang.machineFormat true`
for an agent-driven session. -/
register_option pythia.bang.machineFormat : Bool := {
  defValue := false
  descr := "When true, `pythia?` emits a `[pythia.bang.result]` or `[pythia.bang.failure]` tagged log line with structured JSON for agent-loop consumption. Default false for interactive use."
}

/-- A single rung in the `pythia!` ladder.

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
kairos-sdk companion (`kairos.lean_cycle.cycle_prove`), not here.

Rung 1 wires the `@[stat_simp]` curated simp set (ATH-754 / ATH-758)
in front of bare `simp` so every downstream rung sees a properly-
normalized goal: `ENNReal.toReal` round-trips collapsed, indicator
literals folded, conditional-expectation pushes applied. -/
def buildRungs : MetaM (Array Rung) := do
  let r1 : TSyntax `tactic ← `(tactic|
    first
      | (stat_simp; done)
      | (simp only [stat_simp]; done)
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
    ⟨"stat_simp",       "@[stat_simp] (ATH-754) + core simp closure",     r1⟩,
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

/-- `pythia!` — fire the full hammer ladder; first rung to close wins.

Renamed from `pythia!!` in ATH-756 to match the Lean idiom (`simp!`,
`field_simp!`). The legacy spelling survives as a deprecated alias
for one minor version. -/
syntax (name := pythiaBang) "pythia!" : tactic

/-- `pythia!!` — DEPRECATED alias for `pythia!` (ATH-756). Emits a
deprecation warning on use; will be removed in the next minor
version. Migrate to `pythia!` everywhere; the semantics are
identical. -/
syntax (name := pythiaBangBangDeprecated) "pythia!!" : tactic

/-- `pythia?` — verbose `pythia!`. Logs the closing rung plus
per-rung timing for every rung tried.

Renamed from `pythia!?` in ATH-756 to match `apply?` / `rw?` /
`simp?` — the `?` suffix universally means "show me what you did".
Replaces the previous verbose-of-plain-`pythia` tactic; the new
verbose ladder is strictly more informative because it reports
EVERY rung tried, including the plain-`pythia` rung at slot 5. -/
syntax (name := pythiaBangVerbose) "pythia?" : tactic

/-- `pythia!?` — DEPRECATED alias for `pythia?` (ATH-756). Emits a
deprecation warning on use; will be removed in the next minor
version. -/
syntax (name := pythiaBangVerboseDeprecated) "pythia!?" : tactic

/-- Suggested manual tactics indexed by the failing rung name. When
`pythia!` exhausts the ladder, the failure diagnostic appends a
"things to try" hint pointing the user at hand-tactics that operate
in the same family as the rung that just failed. -/
private def rungHint (rungId : String) : String :=
  match rungId with
  | "stat_simp"      => "try `simp [stat_simp]; <follow-up>` and inspect the residual goal"
  | "linarith_chain" => "try `nlinarith [<aux hypotheses>]` or `polyrith` with explicit lemmas"
  | "positivity"     => "case-split on the sign of relevant subterms; positivity needs concrete bounds"
  | "aesop_pythia"   => "tag the missing lemma with `@[stat_lemma]` or `@[aesop safe]` (ruleset Pythia)"
  | "pythia"         => "the cascade fell through — supply the lemma directly via `exact`"
  | "z3_check"       => "rewrite to QF_LRA shape: linear arithmetic over ℝ, no transcendentals"
  | "cvc5_check"     => "rewrite to QF_BV / QF_LRA; CVC5 cannot handle quantifiers without instantiation"
  | "fol_check"      => "supply axioms explicitly as local hypotheses; vampire/e need the relevant facts"
  | "disprove"       => "the goal MAY be vacuously true; check hypotheses are satisfiable"
  | _                => "no hint available"

/-- Core ladder runner shared by `pythia!` and the deprecated alias.
Returns `Unit` on success and throws on full-ladder miss.

On failure: emits a structured per-rung breakdown via `logError`
showing what was tried, how long each rung ran, and a
hand-tactic hint indexed by the LAST rung that was attempted. The
breakdown is silent on the success path — only failures pay the
diagnostic cost. -/
def runPythiaBang : TacticM Unit := do
  let rungs ← liftMetaM buildRungs
  let mut closed := false
  let mut summary : Array String := #[]
  let mut lastTried : Option String := none
  for rung in rungs do
    if closed then break
    let t0 ← IO.monoMsNow
    match ← tryRung rung pythiaBangDefaultHeartbeats with
    | some ms =>
      closed := true
      summary := summary.push s!"  ✓ {rung.id} CLOSED in {ms}ms ({rung.descr})"
    | none =>
      let t1 ← IO.monoMsNow
      summary := summary.push s!"  ✗ {rung.id} failed in {t1 - t0}ms ({rung.descr})"
      lastTried := some rung.id
  unless closed do
    let body := String.intercalate "\n" summary.toList
    let hint := match lastTried with
      | some r => rungHint r
      | none   => "no rung was attempted (ladder is empty)"
    throwError s!"pythia!: no rung closed the goal.\n\
                 \n\
                 Ladder breakdown:\n\
                 {body}\n\
                 \n\
                 Hint (based on last rung tried, `{lastTried.getD "(none)"}`):\n\
                 {hint}\n\
                 \n\
                 For per-rung timing on the SUCCESS path use `pythia?` (verbose).\n\
                 For LLM-augmented closure see `kairos.lean_cycle.cycle_prove` in the kairos-sdk companion."

/-- Core verbose runner shared by `pythia?` and the deprecated alias. -/
def runPythiaBangVerbose : TacticM Unit := do
  let rungs ← liftMetaM buildRungs
  let mut closed := false
  let mut summary : Array String := #[]
  let mut closingRung : Option String := none
  let mut closingMs : Nat := 0
  for rung in rungs do
    if closed then
      summary := summary.push s!"  {rung.id}: skipped (already closed)"
    else
      match ← tryRung rung pythiaBangDefaultHeartbeats with
      | some ms =>
        summary := summary.push s!"  {rung.id}: CLOSED in {ms}ms — {rung.descr}"
        closed := true
        closingRung := some rung.id
        closingMs := ms
      | none =>
        summary := summary.push s!"  {rung.id}: failed — {rung.descr}"
  let body := String.intercalate "\n" summary.toList
  let machineFmt := pythia.bang.machineFormat.get (← getOptions)
  match closingRung with
  | some r =>
    logInfo m!"pythia? — closed by `{r}`. Ladder timing:\n{body}"
    if machineFmt then
      logInfo s!"[pythia.bang.result] \{\"rung\": \"{r}\", \"ms\": {closingMs}}"
  | none =>
    logInfo m!"pythia? — no rung closed. Ladder timing:\n{body}"
    if machineFmt then
      logInfo "[pythia.bang.failure] {\"reason\": \"no_rung_closed\"}"
    throwError "pythia?: no rung closed the goal."

@[tactic pythiaBang] def evalPythiaBang : Tactic := fun stx => do
  match stx with
  | `(tactic| pythia!) => runPythiaBang
  | _ => throwUnsupportedSyntax

@[tactic pythiaBangBangDeprecated] def evalPythiaBangBangDeprecated : Tactic := fun stx => do
  match stx with
  | `(tactic| pythia!!) =>
    logWarning "`pythia!!` is deprecated (ATH-756); use `pythia!` instead. The legacy spelling will be removed in the next minor version."
    runPythiaBang
  | _ => throwUnsupportedSyntax

@[tactic pythiaBangVerbose] def evalPythiaBangVerbose : Tactic := fun stx => do
  match stx with
  | `(tactic| pythia?) => runPythiaBangVerbose
  | _ => throwUnsupportedSyntax

@[tactic pythiaBangVerboseDeprecated] def evalPythiaBangVerboseDeprecated : Tactic := fun stx => do
  match stx with
  | `(tactic| pythia!?) =>
    logWarning "`pythia!?` is deprecated (ATH-756); use `pythia?` instead. The legacy spelling will be removed in the next minor version."
    runPythiaBangVerbose
  | _ => throwUnsupportedSyntax

end Pythia
