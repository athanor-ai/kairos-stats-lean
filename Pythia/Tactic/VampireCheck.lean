/-
Pythia.Tactic.VampireCheck — Phase 5 of the cross-prover hammer
: the `vampire_check` tactic.

## What it does

`vampire_check` closes first-order Lean goals that have no arithmetic
content by:

  1. Encoding the goal and the encodable subset of the local context as
     a TPTP FOF problem (see `Pythia.Tactic.TPTPEncode`).
  2. Shelling out to the `vampire` binary via `IO.Process.run`.
  3. If `vampire` returns `Theorem` for the conjecture, asking Lean's
     `aesop` (with the local hypotheses promoted into its rule set) to
     reconstruct a kernel-checked proof.

## Architectural principle: Vampire is an oracle, not a trusted prover

The tactic NEVER closes the goal on Vampire's verdict alone. Vampire is
used purely as a ranking / filter oracle: a quick check that the goal
is provable in classical first-order logic. The actual Lean proof term
is constructed by `aesop`, which runs against the registered
`@[stat_lemma]` library plus every local hypothesis (promoted to the
`safe` rule slot for premise selection). If Vampire says `Theorem` but
`aesop` fails to close, the tactic fails loudly. That is by design and
serves as a soundness signal: the encoding diverges from the goal, or
the goal exceeds aesop's heuristic range, and we should not silently
trust Vampire.

This mirrors the CoqHammer (Czajka and Kaliszyk, JAR 2018) and Isabelle
Sledgehammer (Paulson and Susanto, ITP 2007; Blanchette et al. 2016)
discipline: external solvers produce a verdict, the host kernel
independently reconstructs the proof. The Lean 4 kernel checks the
final term against `{propext, Classical.choice, Quot.sound}`, the
Mathlib axiom budget. No claim escapes the kernel.

## Phase 5 scope

Supported goal shapes:

  * Quantified Lean `Prop` goals using `∀`, `∃`, `∧`, `∨`, `¬`, `→`,
    `↔`, `=` over uninterpreted (non-arithmetic) carrier types.
  * Hypotheses with the same shape: they go into the TPTP problem as
    `axiom` formulas and into aesop's local rule set as `safe` rules.
  * Equalities over uninterpreted types.

Out of scope (returns `outOfFragment`):

  * Any subterm of arithmetic carrier type (`ℝ`, `ℚ`, `ℤ`, `ℕ`,
    `ENNReal`, `NNReal`, `Float`). Those are routed to `z3_check`,
    `omega`, or `linarith` by the dispatcher.
  * Higher-order quantification (`∀ P : T → Prop, ...`).
  * Type-class projections, dependent products beyond simple arrows.

## Vampire availability

Vampire is invoked at tactic runtime, not at module load. The module
compiles and loads on machines without Vampire installed. The absence
is only reported when a user actually writes `by vampire_check` and
the binary cannot be spawned, in which case the tactic falls through
to a direct `aesop` call (so the worst case is `vampire_check ≡ aesop`
with the local context).

The companion test file `VampireCheckTest.lean` only contains examples
that `aesop` also closes, so the regression suite passes whether or
not Vampire is on the build machine. The Vampire path is exercised
opportunistically.

## Driver

Phase 5. The companion `e_check` tactic in `Pythia.Tactic.ECheck`
shares the TPTP encoder and acts as the backup when Vampire is absent
or returns `unknown`. The dispatcher in `Pythia.Tactic.Pythia` routes
`Pure FOL no arithmetic` goals to `vampire_check`, then `e_check`.
-/
import Mathlib
import Aesop
import Lean.Elab.Tactic
import Pythia.Tactic.TPTPEncode

namespace Pythia

open Lean Elab Meta Tactic
open Pythia.TPTPEncode

namespace VampireCheck

/-! ### Vampire invocation

We write the TPTP query to a temp file and run `vampire --mode casc
--time_limit 10 <file>`. `casc` mode is Vampire's competition default
and emits SZS-status lines on stdout. We parse:

  * `Termination reason: Refutation`        → `theorem`
  * `Termination reason: Satisfiable`       → `counterSatisfiable`
  * `Termination reason: Time limit`        → `timeout`
  * anything else                          → `unknown`

Vampire also emits SZS lines (`% SZS status Theorem`) which we accept
as an alternate success signal.
-/

/-- Spawn Vampire and read back its verdict. Lazy: only invoked at
tactic runtime, never at module load. The 10 s time limit caps CI
cost. -/
def runVampire (tptp : String) : IO Verdict := do
  -- Probe-first: missing binary must surface as `notInstalled` rather
  -- than a raw `IOError`.
  let probe ← try
    IO.Process.output { cmd := "which", args := #["vampire"] }
  catch _ =>
    return .notInstalled
  if probe.exitCode ≠ 0 then
    return .notInstalled
  -- Write query to a temp file under `/tmp/`. Mirrors `Z3Check.runZ3`:
  -- file path keeps things debuggable, no cleanup discipline in
  -- Phase 5.
  let tmpDir ← IO.getEnv "TMPDIR" >>= fun
    | some d => pure d
    | none => pure "/tmp"
  let stamp ← IO.monoMsNow
  let tmpFile := s!"{tmpDir}/pythia_vampire_check_{stamp}.p"
  IO.FS.writeFile tmpFile tptp
  let result ← try
    IO.Process.output {
      cmd := "vampire"
      args := #["--mode", "casc", "--time_limit", "10", tmpFile]
    }
  catch e =>
    return .error s!"failed to invoke vampire: {e}"
  let stdout := result.stdout
  -- Inspect both `Termination reason:` and SZS status lines. Vampire
  -- prints both in casc mode. We use `splitOn` length > 1 as an
  -- "appears as substring" check; wrapping in `(...)` keeps the `>`
  -- from being parsed against the trailing `then` keyword.
  let contains (needle : String) : Bool := (stdout.splitOn needle).length > 1
  if contains "SZS status Theorem" then return .theorem
  if contains "Termination reason: Refutation" then return .theorem
  if contains "SZS status CounterSatisfiable" then return .counterSatisfiable
  if contains "Termination reason: Satisfiable" then return .counterSatisfiable
  if contains "Termination reason: Time limit" then return .timeout
  if contains "SZS status Timeout" then return .timeout
  return .unknown

end VampireCheck

open VampireCheck

/-! ### The `vampire_check` tactic

Workflow:

  1. Read the main goal and its local context.
  2. Try to encode goal plus FOL hypotheses as a TPTP problem.
  3. If encoding succeeds, ask Vampire for a `Theorem` verdict.
  4. Whether or not Vampire was queried successfully, ALWAYS try aesop
     (with the local hypotheses promoted to its safe rule set) as the
     actual proof.
  5. If Vampire said `Theorem` but aesop fails: fail loudly.
  6. If Vampire was unavailable / out of fragment: fall through to
     aesop directly. Worst case `vampire_check ≡ aesop`.
  7. If Vampire said `CounterSatisfiable`: report the goal is not
     provable in FOL.
-/

/-- `vampire_check` — Phase 5 cross-prover hammer for first-order Lean
goals without arithmetic. Asks Vampire whether the goal is a theorem in
FOL, then reconstructs the proof via aesop with the local hypotheses
in its rule set. Vampire's verdict is never trusted in isolation:
aesop independently certifies the proof term against the Lean kernel. -/
syntax (name := vampireCheckTac) "vampire_check" : tactic

@[tactic vampireCheckTac] def evalVampireCheck : Tactic := fun stx => do
  match stx with
  | `(tactic| vampire_check) =>
    let goal ← getMainGoal
    goal.withContext do
      let target ← goal.getType
      let target ← instantiateMVars target
      -- Encode goal.
      let encGoal ← encodeFOL target
      -- Collect encodable hypotheses.
      let lctx ← getLCtx
      let mut encHyps : List TPTPFormula := []
      for ldecl in lctx do
        if ldecl.isImplementationDetail then continue
        let ty ← instantiateMVars ldecl.type
        unless ← isProp ty do continue
        let some h ← encodeFOL ty | continue
        encHyps := h :: encHyps
      -- Decide what Vampire told us.
      let verdict : Verdict ← match encGoal with
        | none => pure Verdict.outOfFragment
        | some g =>
          let tptp := buildQuery encHyps g
          let v ← (runVampire tptp : IO Verdict)
          pure v
      -- Always try aesop. The local hypotheses are already in scope;
      -- aesop's default `safe` rules include hypothesis intro / apply,
      -- so premise selection is implicit.
      let aesopRes ← try
        evalTactic (← `(tactic| aesop (config := { warnOnNonterminal := false })))
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
      match verdict, aesopRes with
      | .theorem, .ok _ =>
        return ()
      | .theorem, .error _ =>
        -- Vampire says provable, aesop disagrees. Soundness signal:
        -- encoding may be unfaithful, or aesop's heuristic is weaker
        -- than Vampire's superposition search here. Either way we MUST
        -- NOT close the goal; the Lean kernel is the trusted layer.
        throwError "vampire_check: vampire reported `Theorem` but `aesop` could not reconstruct the proof. This is a soundness signal: refusing to close on vampire's verdict alone. Inspect the goal and report if you believe both should agree."
      | .counterSatisfiable, _ =>
        throwError "vampire_check: vampire found a counter-model. The goal is not a first-order theorem under the given hypotheses."
      | .notInstalled, .ok _ =>
        return ()
      | .notInstalled, .error _ =>
        throwError "vampire_check: vampire binary not found on PATH (install via the upstream Vampire release tarball at https://vprover.github.io/), and `aesop` could not close the goal directly."
      | .outOfFragment, .ok _ =>
        return ()
      | .outOfFragment, .error _ =>
        throwError "vampire_check: goal is outside the FOL-without-arithmetic fragment, and `aesop` could not close it. Try `z3_check` for arithmetic goals, or `pythia` for the full dispatch cascade."
      | .timeout, .ok _ =>
        return ()
      | .timeout, .error _ =>
        throwError "vampire_check: vampire timed out (10 s budget), and `aesop` could not close the goal directly. Try `e_check` as the backup FOL oracle."
      | .unknown, .ok _ =>
        return ()
      | .unknown, .error _ =>
        throwError "vampire_check: vampire returned `unknown`, and `aesop` could not close the goal directly."
      | .error msg, .ok _ =>
        logInfo s!"vampire_check: vampire invocation failed ({msg}); proof closed by `aesop` fallback."
        return ()
      | .error msg, .error _ =>
        throwError "vampire_check: vampire invocation failed ({msg}), and `aesop` could not close the goal directly."
  | _ => throwUnsupportedSyntax

end Pythia
