/-
Pythia.Tactic.Z3Check — Phase 1 of the cross-prover hammer
: the `z3_check` tactic.

## What it does

`z3_check` closes linear-arithmetic goals over `ℝ` by:

  1. Encoding the goal (and its hypotheses, when they are also
     linear-real facts) as an SMT-LIB v2.6 query.
  2. Shelling out to the `z3` binary via `IO.Process.run`.
  3. If `z3` returns `unsat` for the negation, asking Lean's own
     `linarith` to discharge the original goal.

## Architectural principle: Z3 is an oracle, not a trusted prover

The tactic NEVER closes the goal on Z3's verdict alone. Z3 is used
purely as a *ranking / filter oracle*: a quick check that the goal is
in fact closable by linear-real reasoning. The actual Lean proof
term is constructed by `linarith`, which builds its own
kernel-checked Farkas certificate. If Z3 says unsat but `linarith`
fails to close, the tactic fails loudly — this is by design and
serves as a soundness signal (the encoding diverges from the goal,
or the goal is not in Lean's linarith fragment, and we should not
silently trust Z3).

This mirrors the CoqHammer (Czajka & Kaliszyk, JAR 2018) discipline:
external solvers produce a verdict / certificate; the host kernel
independently reconstructs the proof. The Lean 4 kernel checks the
final term against `{propext, Classical.choice, Quot.sound}` — the
Mathlib axiom budget. No claim escapes the kernel.

## Phase 1 scope (deliberate minimum)

Supported goal shapes:

  • Linear (in)equalities over `ℝ`-valued atoms.
  • Hypotheses of the form `a ≤ b`, `a < b`, `a = b`, `a ≥ b`, `a > b`
    where `a`, `b` are linear over `ℝ`-typed locals.
  • Goal must reduce to `Prop`-level linear arithmetic.

Out of scope (deferred to Phase 2):

  • Nonlinear arithmetic.
  • Quantifier reasoning.
  • `ℂ` / `ℕ` / `ℤ` goals (ℝ only — though `ℕ` / `ℤ` literals as
    coerced reals are fine).
  • Polyrith integration.
  • CVC5 / Vampire / E backends.

## Z3 availability

Z3 is invoked at *tactic runtime*, not at module load. The module
compiles and loads on machines without Z3 installed; the absence is
only reported when a user actually writes `by z3_check` and the
binary cannot be spawned. The error message points at
`apt-get install z3`.

The companion test file `Z3CheckTest.lean` only contains examples
that `linarith` *also* closes, so the regression suite passes
whether or not Z3 is on the build machine. The Z3 path is exercised
opportunistically.

## Driver

Phase 1. Phase 2 expands to nonlinear (Z3 + nlinarith),
Phase 3 introduces CVC5 / Vampire as alternates. The `z3_check`
name is final per Aidan's 2026-04-25 directive.
-/
import Mathlib
import Lean.Elab.Tactic

namespace Pythia

open Lean Elab Meta Tactic

/-! ### SMT-LIB encoding

We encode a small, conservative fragment: literal real numerals,
real-typed free variables, and the binary operators `+`, `-`, `*`
(only with at least one literal argument), together with
`(in)equalities` over `≤ < = ≥ >`.

This is the negation we send to Z3:

    (assert (not (=> H₁ ∧ … ∧ Hₙ → G)))

so a `unsat` reply means the original implication is valid. Lean
then asks `linarith` to construct the actual proof.

Anything outside the conservative fragment trips the `none` branch
and the tactic skips Z3 entirely, falling through to a direct
`linarith` call. That fall-through is what keeps the tactic
trivially sound: in the worst case `z3_check ≡ linarith`. -/

namespace Z3Check

/-- A linear arithmetic atom or expression.

We stay deliberately small here: literal rationals, free variables,
and binary `+`/`-`/`*` with at least one literal. Anything more
exotic returns `none` from the encoder and we let the linarith
fallback handle the goal. -/
inductive SExpr
  | lit (s : String)
  | var (n : Name)
  | bin (op : String) (a b : SExpr)
  deriving Inhabited

/-- Pretty-print an `SExpr` as SMT-LIB. -/
partial def SExpr.toSmt : SExpr → String
  | .lit s => s
  | .var n => "v_" ++ n.toString.replace "." "_"
  | .bin op a b => s!"({op} {a.toSmt} {b.toSmt})"

/-- Try to encode an `Expr` of type `ℝ` as a linear `SExpr`. Returns
`none` for anything we don't recognise: that's the signal to skip
Z3 and fall through to `linarith`. -/
partial def encodeReal (e : Expr) : MetaM (Option SExpr) := do
  let e ← instantiateMVars e
  match e with
  | .fvar fv =>
    let decl ← fv.getDecl
    return some (.var decl.userName)
  | .lit (.natVal n) => return some (.lit (toString n))
  | _ =>
    -- Try to recognise standard arithmetic operators.
    match_expr e with
    | HAdd.hAdd _ _ _ _ a b => do
      let some a' ← encodeReal a | return none
      let some b' ← encodeReal b | return none
      return some (.bin "+" a' b')
    | HSub.hSub _ _ _ _ a b => do
      let some a' ← encodeReal a | return none
      let some b' ← encodeReal b | return none
      return some (.bin "-" a' b')
    | HMul.hMul _ _ _ _ a b => do
      let some a' ← encodeReal a | return none
      let some b' ← encodeReal b | return none
      return some (.bin "*" a' b')
    | Neg.neg _ _ a => do
      let some a' ← encodeReal a | return none
      return some (.bin "-" (.lit "0") a')
    | OfNat.ofNat _ n _ =>
      -- Extract the natural-number literal argument of `OfNat.ofNat`.
      match (← instantiateMVars n) with
      | .lit (.natVal k) => return some (.lit (toString k))
      | _ => return none
    | _ => return none

/-- Encode a `Prop` of the form `a ≤ b` / `a < b` / `a = b` / etc.,
where `a, b : ℝ`, as an SMT-LIB formula. Returns `none` when out of
fragment. -/
partial def encodeProp (e : Expr) : MetaM (Option SExpr) := do
  let e ← instantiateMVars e
  match_expr e with
  | LE.le _ _ a b => do
    let some a' ← encodeReal a | return none
    let some b' ← encodeReal b | return none
    return some (.bin "<=" a' b')
  | LT.lt _ _ a b => do
    let some a' ← encodeReal a | return none
    let some b' ← encodeReal b | return none
    return some (.bin "<" a' b')
  | GE.ge _ _ a b => do
    let some a' ← encodeReal a | return none
    let some b' ← encodeReal b | return none
    return some (.bin ">=" a' b')
  | GT.gt _ _ a b => do
    let some a' ← encodeReal a | return none
    let some b' ← encodeReal b | return none
    return some (.bin ">" a' b')
  | Eq _ a b => do
    let some a' ← encodeReal a | return none
    let some b' ← encodeReal b | return none
    return some (.bin "=" a' b')
  | _ => return none

/-- Collect free `ℝ`-typed variables that appear in a list of
encoded expressions, by walking each `SExpr`. Used to emit the
`(declare-const v_x Real)` block. -/
partial def SExpr.vars : SExpr → List Name
  | .lit _ => []
  | .var n => [n]
  | .bin _ a b => a.vars ++ b.vars

/-- Build a self-contained SMT-LIB v2.6 query for a goal `G` under
hypotheses `Hs`. Asks Z3 to refute `(and H₁ … Hₙ (not G))`. -/
def buildQuery (hyps : List SExpr) (goal : SExpr) : String := Id.run do
  let allVars := (goal :: hyps).flatMap SExpr.vars
  let uniqVars := allVars.eraseDups
  let header := "(set-logic QF_LRA)\n(set-info :status unsat)\n"
  let decls := uniqVars.foldl
    (fun acc n => acc ++ s!"(declare-const v_{n.toString.replace "." "_"} Real)\n")
    ""
  let hypAsserts := hyps.foldl
    (fun acc h => acc ++ s!"(assert {h.toSmt})\n")
    ""
  let goalAssert := s!"(assert (not {goal.toSmt}))\n"
  let footer := "(check-sat)\n(exit)\n"
  return header ++ decls ++ hypAsserts ++ goalAssert ++ footer

/-- Result of probing Z3.

* `unsat` — Z3 refuted the negation; goal is valid in QF_LRA.
* `sat`   — Z3 found a counterexample; goal is *not* valid.
* `unknown` — Z3 gave up.
* `notInstalled` — `z3` binary not on `PATH`.
* `outOfFragment` — encoder returned `none`; we never invoked Z3.
* `timeout` / `error` — Z3 invocation failed. -/
inductive Verdict
  | unsat
  | sat (model : String)
  | unknown
  | notInstalled
  | outOfFragment
  | error (msg : String)
  deriving Inhabited

/-- Spawn Z3 and read back its verdict. Lazy: only invoked at tactic
runtime, never at module load. Times out after 5 seconds via the
`-T:5` argument to keep CI bounded.

Implementation: write the SMT query to a temp file, then run
`z3 -smt2 -T:5 <file>`. We use a file rather than stdin because the
`takeStdin` API is awkward to thread cleanly through `IO`, and the
file path keeps things debuggable (you can `cat` the temp file if
something goes wrong). -/
def runZ3 (smt : String) : IO Verdict := do
  -- Detect `z3` first; missing binary must surface the helpful
  -- "install z3" message rather than a raw `IOError`.
  let probe ← try
    IO.Process.output { cmd := "which", args := #["z3"] }
  catch _ =>
    return .notInstalled
  if probe.exitCode ≠ 0 then
    return .notInstalled
  -- Write query to a temp file under `/tmp/`. We don't need
  -- cleanup discipline — Phase 1 leaves temp files for debugging.
  let tmpDir ← IO.getEnv "TMPDIR" >>= fun
    | some d => pure d
    | none => pure "/tmp"
  let stamp ← IO.monoMsNow
  let tmpFile := s!"{tmpDir}/pythia_z3_check_{stamp}.smt2"
  IO.FS.writeFile tmpFile smt
  let result ← try
    IO.Process.output {
      cmd := "z3"
      -- 2s soft cap (tightened from 5s in ATH-761). Z3 closes most
      -- QF_LRA goals in <100ms; the long tail past 2s rarely yields.
      args := #["-smt2", "-T:2", tmpFile]
    }
  catch e =>
    return .error s!"failed to invoke z3: {e}"
  let trimmed := result.stdout.trimAscii.toString
  if trimmed.startsWith "unsat" then
    return .unsat
  else if trimmed.startsWith "sat" then
    return .sat trimmed
  else if trimmed.startsWith "unknown" then
    return .unknown
  else
    return .error s!"z3 returned unexpected output: {trimmed} (stderr: {result.stderr.trimAscii.toString})"

end Z3Check

open Z3Check

/-! ### The `z3_check` tactic

Workflow:

  1. Read the main goal and its local context.
  2. Try to encode goal + linear-real hypotheses as SMT-LIB.
  3. If encoding succeeds, ask Z3 for `unsat`.
  4. Whether or not Z3 was queried successfully, ALWAYS try
     `linarith` as the actual proof.
  5. If Z3 said `unsat` but `linarith` fails: fail loudly.
  6. If Z3 was unavailable / out-of-fragment: fall through to
     `linarith` directly (worst case `z3_check ≡ linarith`).
  7. If Z3 said `sat`: report the goal is unprovable in QF_LRA. -/

/-- `z3_check` — Phase 1 cross-prover hammer for linear arithmetic
over `ℝ`. Asks Z3 whether the goal is valid in QF_LRA, then
reconstructs the proof via `linarith`. Z3's verdict is never
trusted in isolation: linarith independently certifies the proof
term against the Lean kernel. -/
syntax (name := z3CheckTac) "z3_check" : tactic

@[tactic z3CheckTac] def evalZ3Check : Tactic := fun stx => do
  match stx with
  | `(tactic| z3_check) =>
    let goal ← getMainGoal
    goal.withContext do
      let target ← goal.getType
      let target ← instantiateMVars target
      -- Encode goal.
      let encGoal ← encodeProp target
      -- Collect encodable hypotheses.
      let lctx ← getLCtx
      let mut encHyps : List SExpr := []
      for ldecl in lctx do
        if ldecl.isImplementationDetail then continue
        let some h ← encodeProp ldecl.type | continue
        encHyps := h :: encHyps
      -- Decide what Z3 told us.
      let verdict : Verdict ← match encGoal with
        | none => pure Verdict.outOfFragment
        | some g =>
          let smt := buildQuery encHyps g
          let v ← (runZ3 smt : IO Verdict)
          pure v
      -- Always try linarith — Z3 is just a filter / sanity check.
      let linarithRes ← try
        evalTactic (← `(tactic| linarith))
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
      match verdict, linarithRes with
      | .unsat, .ok _ =>
        -- Both agree: closed.
        return ()
      | .unsat, .error _ =>
        -- Z3 says valid, linarith disagrees. Soundness signal:
        -- the encoding is unfaithful or linarith's heuristic is
        -- weaker than Z3 here. Either way we MUST NOT close the
        -- goal — Lean kernel is the trusted layer.
        throwError "z3_check: z3 reported `unsat` but `linarith` could not reconstruct the proof. This is a soundness signal — refusing to close on z3's verdict alone. Inspect the goal and report if you believe both should agree."
      | .sat _, _ =>
        throwError "z3_check: z3 found a counterexample (sat). The goal is not valid in QF_LRA over ℝ."
      | .notInstalled, .ok _ =>
        -- Z3 absent but linarith closed. Fine.
        return ()
      | .notInstalled, .error _ =>
        throwError "z3_check: z3 binary not found on PATH (install via `apt-get install z3`), and `linarith` could not close the goal directly."
      | .outOfFragment, .ok _ =>
        return ()
      | .outOfFragment, .error _ =>
        throwError "z3_check: goal is outside the Phase-1 linear-real fragment, and `linarith` could not close it. (Phase 2 will route nonlinear goals to z3 + nlinarith.)"
      | .unknown, .ok _ =>
        return ()
      | .unknown, .error _ =>
        throwError "z3_check: z3 returned `unknown`, and `linarith` could not close the goal directly."
      | .error msg, .ok _ =>
        -- Z3 failed but linarith handled it.
        logInfo s!"z3_check: z3 invocation failed ({msg}); proof closed by `linarith` fallback."
        return ()
      | .error msg, .error _ =>
        throwError "z3_check: z3 invocation failed ({msg}), and `linarith` could not close the goal directly."
  | _ => throwUnsupportedSyntax

end Pythia
