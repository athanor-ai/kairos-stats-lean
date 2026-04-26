/-
Pythia.Tactic.ECheck — Phase 5 of the cross-prover hammer
: the `e_check` tactic (backup FOL oracle).

## What it does

`e_check` closes first-order Lean goals that have no arithmetic
content by:

  1. Encoding the goal and the encodable subset of the local context as
     a TPTP FOF problem (see `Pythia.Tactic.TPTPEncode`).
  2. Shelling out to the `eprover` binary via `IO.Process.run`.
  3. If E returns `# SZS status Theorem`, asking Lean's `aesop` (with
     the local hypotheses promoted into its rule set) to reconstruct a
     kernel-checked proof.

## Architectural principle: E is an oracle, not a trusted prover

The tactic NEVER closes the goal on E's verdict alone. E is used as
a ranking / filter oracle: a quick check that the goal is provable in
classical first-order logic. The actual Lean proof term is constructed
by `aesop`. If E says `Theorem` but `aesop` fails to close, the tactic
fails loudly. That is the same soundness signal pattern as
`vampire_check` and `z3_check`: external solvers produce a verdict,
the host kernel independently reconstructs the proof. The Lean 4
kernel checks the final term against
`{propext, Classical.choice, Quot.sound}`.

## Phase 5 scope

Same fragment as `vampire_check`. See `Pythia.Tactic.VampireCheck` and
`Pythia.Tactic.TPTPEncode` for the supported / out-of-fragment goal
shapes. Both adapters share the encoder.

## E availability

E is invoked at tactic runtime, not at module load. The module
compiles and loads on machines without E installed. The companion
test file `ECheckTest.lean` only contains examples that `aesop` also
closes.

## Driver

Phase 5 backup. The dispatcher in `Pythia.Tactic.Pythia` routes
`Pure FOL no arithmetic` goals to `vampire_check` first, then `e_check`
if Vampire is absent or returns `unknown`.
-/
import Mathlib
import Aesop
import Lean.Elab.Tactic
import Pythia.Tactic.TPTPEncode

namespace Pythia

open Lean Elab Meta Tactic
open Pythia.TPTPEncode

namespace ECheck

/-! ### E invocation

We run `eprover --auto-schedule --tptp3-format --soft-cpu-limit=10`
on the temp file. E's verdict format is the SZS-status line:

  * `# SZS status Theorem`              → `theorem`
  * `# SZS status CounterSatisfiable`   → `counterSatisfiable`
  * `# SZS status ResourceOut`          → `timeout`
  * `# SZS status GaveUp`               → `unknown`

E sometimes prints `Proof found!` instead, which we accept as a
secondary success signal.
-/

/-- Spawn E and read back its verdict. Lazy: only invoked at tactic
runtime. The 10 s soft CPU limit caps CI cost. -/
def runE (tptp : String) : IO Verdict := do
  -- Probe-first: missing binary surfaces as `notInstalled` rather
  -- than a raw `IOError`.
  let probe ← try
    IO.Process.output { cmd := "which", args := #["eprover"] }
  catch _ =>
    return .notInstalled
  if probe.exitCode ≠ 0 then
    return .notInstalled
  let tmpDir ← IO.getEnv "TMPDIR" >>= fun
    | some d => pure d
    | none => pure "/tmp"
  let stamp ← IO.monoMsNow
  let tmpFile := s!"{tmpDir}/pythia_e_check_{stamp}.p"
  IO.FS.writeFile tmpFile tptp
  let result ← try
    IO.Process.output {
      cmd := "eprover"
      args := #[
        "--auto-schedule",
        "--tptp3-format",
        "--soft-cpu-limit=10",
        tmpFile
      ]
    }
  catch e =>
    return .error s!"failed to invoke eprover: {e}"
  let stdout := result.stdout
  let contains (needle : String) : Bool := (stdout.splitOn needle).length > 1
  if contains "SZS status Theorem" then return .theorem
  if contains "Proof found!" then return .theorem
  if contains "SZS status CounterSatisfiable" then return .counterSatisfiable
  if contains "SZS status ResourceOut" then return .timeout
  if contains "SZS status Timeout" then return .timeout
  if contains "SZS status GaveUp" then return .unknown
  return .unknown

end ECheck

open ECheck

/-! ### The `e_check` tactic

Same workflow as `vampire_check`, with the `eprover` binary instead of
`vampire`. See `Pythia.Tactic.VampireCheck` for the workflow rationale.
-/

/-- `e_check` — Phase 5 backup FOL oracle. Asks E whether the goal is
a theorem in FOL, then reconstructs the proof via aesop with the local
hypotheses in its rule set. E's verdict is never trusted in isolation:
aesop independently certifies the proof term against the Lean kernel. -/
syntax (name := eCheckTac) "e_check" : tactic

@[tactic eCheckTac] def evalECheck : Tactic := fun stx => do
  match stx with
  | `(tactic| e_check) =>
    let goal ← getMainGoal
    goal.withContext do
      let target ← goal.getType
      let target ← instantiateMVars target
      let encGoal ← encodeFOL target
      let lctx ← getLCtx
      let mut encHyps : List TPTPFormula := []
      for ldecl in lctx do
        if ldecl.isImplementationDetail then continue
        let ty ← instantiateMVars ldecl.type
        unless ← isProp ty do continue
        let some h ← encodeFOL ty | continue
        encHyps := h :: encHyps
      let verdict : Verdict ← match encGoal with
        | none => pure Verdict.outOfFragment
        | some g =>
          let tptp := buildQuery encHyps g
          let v ← (runE tptp : IO Verdict)
          pure v
      let aesopRes ← try
        evalTactic (← `(tactic| aesop (config := { warnOnNonterminal := false })))
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
      match verdict, aesopRes with
      | .theorem, .ok _ =>
        return ()
      | .theorem, .error _ =>
        throwError "e_check: eprover reported `Theorem` but `aesop` could not reconstruct the proof. This is a soundness signal: refusing to close on E's verdict alone. Inspect the goal and report if you believe both should agree."
      | .counterSatisfiable, _ =>
        throwError "e_check: eprover found a counter-model. The goal is not a first-order theorem under the given hypotheses."
      | .notInstalled, .ok _ =>
        return ()
      | .notInstalled, .error _ =>
        throwError "e_check: eprover binary not found on PATH (install via `apt-get install eprover` or the upstream E release at https://www.eprover.org/), and `aesop` could not close the goal directly."
      | .outOfFragment, .ok _ =>
        return ()
      | .outOfFragment, .error _ =>
        throwError "e_check: goal is outside the FOL-without-arithmetic fragment, and `aesop` could not close it. Try `z3_check` for arithmetic goals, or `pythia` for the full dispatch cascade."
      | .timeout, .ok _ =>
        return ()
      | .timeout, .error _ =>
        throwError "e_check: eprover timed out (10 s budget), and `aesop` could not close the goal directly."
      | .unknown, .ok _ =>
        return ()
      | .unknown, .error _ =>
        throwError "e_check: eprover returned `unknown` / `GaveUp`, and `aesop` could not close the goal directly."
      | .error msg, .ok _ =>
        logInfo s!"e_check: eprover invocation failed ({msg}); proof closed by `aesop` fallback."
        return ()
      | .error msg, .error _ =>
        throwError "e_check: eprover invocation failed ({msg}), and `aesop` could not close the goal directly."
  | _ => throwUnsupportedSyntax

end Pythia
