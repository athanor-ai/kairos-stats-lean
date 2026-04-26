/-
Pythia.Tactic.CVC5Check : Phase 2 of the cross-prover hammer
: the `cvc5_check` tactic.

## What it does

`cvc5_check` closes two distinct fragments by routing each through
the appropriate Lean reconstruction tactic:

  1. Bit-vector goals over `BitVec n`. Encoded as SMT-LIB v2.6 in
     the QF_BV logic, dispatched to `cvc5`, reconstructed with
     `bv_decide`.
  2. Linear-real arithmetic over `ℝ`. Encoded in QF_LRA, dispatched
     to `cvc5`, reconstructed with `linarith`. This path is the
     CVC5 backup to `z3_check` from the dispatch table in
     `docs/sledgehammer_dispatch.md`.

CVC5 (Barbosa, Barrett, Brain, Kremer, Lachnitt, Mann, Mohamed,
Mohamed, Niemetz, Notzli, Ozdemir, Preiner, Reynolds, Sheng,
Tinelli, Zohar, TACAS 2022) is the SMT solver complement to Z3.
It is the primary CVC5-side backend for QF_BV (bit-vectors) and
the backup for QF_LRA in the pythia dispatch cascade.

## Architectural principle: CVC5 is an oracle, not a trusted prover

The tactic NEVER closes the goal on CVC5's verdict alone. CVC5 is
used purely as a ranking / filter oracle: a quick check that the
goal is in fact closable by the corresponding Lean tactic. The
actual proof term is constructed by `bv_decide` (for QF_BV) or
`linarith` (for QF_LRA). Both reconstructors build their own
kernel-checked certificates: `bv_decide` produces an LRAT
refutation that the kernel verifies, and `linarith` produces a
Farkas certificate. If CVC5 says `unsat` but reconstruction fails,
the tactic fails loudly. That is by design and serves as a
soundness signal: the encoding diverges from the goal, or the
goal exceeds the reconstructor's heuristic range, and we should
not silently trust CVC5.

This mirrors the CoqHammer (Czajka and Kaliszyk, JAR 2018) and
Isabelle Sledgehammer (Paulson and Susanto, ITP 2007; Blanchette
et al. 2016) discipline: external solvers produce a verdict, the
host kernel independently reconstructs the proof. The Lean 4
kernel checks the final term against `{propext, Classical.choice,
Quot.sound}`, the Mathlib axiom budget. No claim escapes the
kernel.

## Phase 2 scope

Supported QF_BV goal shapes:

  * Equalities and (un)signed (in)equalities over `BitVec n` with
    `BitVec.add`, `BitVec.sub`, `BitVec.mul`, `BitVec.and`,
    `BitVec.or`, `BitVec.xor`, `BitVec.ult`, `BitVec.ule`.
  * Bit-vector literals.
  * Free `BitVec n`-typed locals.

Supported QF_LRA goal shapes (identical to `z3_check`, reusing
its encoder):

  * Linear (in)equalities over `ℝ`-valued atoms.
  * Hypotheses of the form `a ≤ b`, `a < b`, `a = b`, `a ≥ b`,
    `a > b` where `a, b` are linear over `ℝ`-typed locals.

Out of scope (returns `outOfFragment`):

  * Non-linear arithmetic (Phase 3 will route to CVC5 + nlinarith).
  * Quantifier reasoning.
  * `BitVec`-to-`Nat` casts mixed with arithmetic.

## CVC5 availability

CVC5 is invoked at tactic runtime, not at module load. The module
compiles and loads on machines without CVC5 installed. The absence
is only reported when a user actually writes `by cvc5_check` and
the binary cannot be spawned, in which case the tactic falls
through to `bv_decide` / `linarith` directly. So the worst case
is `cvc5_check ≡ bv_decide` (for QF_BV) or `cvc5_check ≡ linarith`
(for QF_LRA), with the appropriate Lean reconstructor doing all of
the work.

The companion test file `CVC5CheckTest.lean` only contains
examples that the Lean reconstructors also close, so the
regression suite passes whether or not the `cvc5` binary is on the
build machine. The CVC5 path is exercised opportunistically.

## Driver

Phase 2. The QF_LRA encoder is shared with `z3_check` via
`Pythia.Z3Check.encodeProp` and friends; the QF_BV encoder is
introduced here. The dispatcher in `Pythia.Tactic.Pythia` routes
bit-vector goals to `cvc5_check` first, and linear-real goals to
`z3_check` first with `cvc5_check` as the backup.
-/
import Mathlib
import Lean.Elab.Tactic
import Pythia.Tactic.Z3Check

namespace Pythia

open Lean Elab Meta Tactic
open Pythia.Z3Check

/-! ### SMT-LIB QF_BV encoding

We encode a small QF_BV fragment: literal `BitVec n` constants,
free `BitVec n`-typed variables, and the standard bit-vector
operators (`bvadd`, `bvsub`, `bvmul`, `bvand`, `bvor`, `bvxor`,
`bvult`, `bvule`) together with equality.

The encoder tracks each bit-vector variable's width so the
SMT-LIB declaration block can emit `(declare-const v_x (_ BitVec n))`
with the right `n`. -/

namespace CVC5Check

/-- A QF_BV expression. We track the bit-width on `var` and `lit`
so the SMT-LIB declaration block can recover it without a second
walk over `Expr`. The declaration block requires a width per
constant, so we surface widths at every leaf. -/
inductive BVExpr
  | lit (s : String) (width : Nat)
  | var (n : Name) (width : Nat)
  | bin (op : String) (a b : BVExpr)
  | rel (op : String) (a b : BVExpr)
  deriving Inhabited

/-- Pretty-print a `BVExpr` as SMT-LIB. -/
partial def BVExpr.toSmt : BVExpr → String
  | .lit s _ => s
  | .var n _ => "v_" ++ n.toString.replace "." "_"
  | .bin op a b => s!"({op} {a.toSmt} {b.toSmt})"
  | .rel op a b => s!"({op} {a.toSmt} {b.toSmt})"

/-- Collect every free variable mentioned in a `BVExpr`, paired with
its bit-width. Used to emit the declare-const block. -/
partial def BVExpr.vars : BVExpr → List (Name × Nat)
  | .lit _ _ => []
  | .var n w => [(n, w)]
  | .bin _ a b => a.vars ++ b.vars
  | .rel _ a b => a.vars ++ b.vars

/-- Try to read the bit-width `n` out of a Lean `BitVec n` type. We
recognise `BitVec n` where `n` reduces to a natural numeral. Returns
`none` for non-`BitVec` types or non-literal widths. -/
partial def readBitVecWidth (ty : Expr) : MetaM (Option Nat) := do
  let ty ← instantiateMVars ty
  match_expr ty with
  | BitVec n =>
    let n ← instantiateMVars n
    match n with
    | .lit (.natVal k) => return some k
    | _ =>
      -- `OfNat.ofNat`-wrapped literal.
      match_expr n with
      | OfNat.ofNat _ k _ =>
        match (← instantiateMVars k) with
        | .lit (.natVal w) => return some w
        | _ => return none
      | _ => return none
  | _ => return none

/-- Try to encode an `Expr` of type `BitVec n` as a `BVExpr`. Returns
`none` for anything we don't recognise: that is the signal to skip
CVC5 and fall through to `bv_decide` (which has its own native
recogniser). -/
partial def encodeBitVec (e : Expr) : MetaM (Option BVExpr) := do
  let e ← instantiateMVars e
  let ty ← inferType e
  let some width ← readBitVecWidth ty | return none
  match e with
  | .fvar fv =>
    let decl ← fv.getDecl
    return some (.var decl.userName width)
  | _ =>
    match_expr e with
    | HAdd.hAdd _ _ _ _ a b => do
      let some a' ← encodeBitVec a | return none
      let some b' ← encodeBitVec b | return none
      return some (.bin "bvadd" a' b')
    | HSub.hSub _ _ _ _ a b => do
      let some a' ← encodeBitVec a | return none
      let some b' ← encodeBitVec b | return none
      return some (.bin "bvsub" a' b')
    | HMul.hMul _ _ _ _ a b => do
      let some a' ← encodeBitVec a | return none
      let some b' ← encodeBitVec b | return none
      return some (.bin "bvmul" a' b')
    | HAnd.hAnd _ _ _ a b => do
      let some a' ← encodeBitVec a | return none
      let some b' ← encodeBitVec b | return none
      return some (.bin "bvand" a' b')
    | HOr.hOr _ _ _ a b => do
      let some a' ← encodeBitVec a | return none
      let some b' ← encodeBitVec b | return none
      return some (.bin "bvor" a' b')
    | HXor.hXor _ _ _ a b => do
      let some a' ← encodeBitVec a | return none
      let some b' ← encodeBitVec b | return none
      return some (.bin "bvxor" a' b')
    | OfNat.ofNat _ n _ =>
      match (← instantiateMVars n) with
      | .lit (.natVal k) =>
        -- `(_ bv<k> <width>)` is the SMT-LIB QF_BV literal syntax.
        return some (.lit s!"(_ bv{k} {width})" width)
      | _ => return none
    | _ => return none

/-- Encode a `Prop` of bit-vector form: `a = b`, `BitVec.ult a b`,
`BitVec.ule a b`, etc. Returns `none` when out of fragment. -/
partial def encodePropBV (e : Expr) : MetaM (Option BVExpr) := do
  let e ← instantiateMVars e
  match_expr e with
  | Eq _ a b => do
    let some a' ← encodeBitVec a | return none
    let some b' ← encodeBitVec b | return none
    return some (.rel "=" a' b')
  | BitVec.ult _ a b => do
    let some a' ← encodeBitVec a | return none
    let some b' ← encodeBitVec b | return none
    return some (.rel "bvult" a' b')
  | BitVec.ule _ a b => do
    let some a' ← encodeBitVec a | return none
    let some b' ← encodeBitVec b | return none
    return some (.rel "bvule" a' b')
  | _ => return none

/-- A coarse BitVec-shape detector. Returns `true` if the proposition
mentions `BitVec n` at the top-level of an `Eq`, `BitVec.ult`, or
`BitVec.ule`, regardless of whether the operands are encodable in
the conservative QF_BV fragment. We use this to route to the
`bv_decide` reconstruction path even when the SMT encoding gives up. -/
partial def goalLooksLikeBV (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  match_expr e with
  | Eq _ a _ =>
    let ty ← inferType a
    let some _ ← readBitVecWidth ty | return false
    return true
  | BitVec.ult _ _ _ => return true
  | BitVec.ule _ _ _ => return true
  | _ => return false

/-- Build a self-contained SMT-LIB v2.6 query in the QF_BV logic for
a goal `G` under hypotheses `Hs`. Asks CVC5 to refute
`(and H₁ ... Hₙ (not G))`. -/
def buildQueryQF_BV (hyps : List BVExpr) (goal : BVExpr) : String := Id.run do
  let allVars := (goal :: hyps).flatMap BVExpr.vars
  -- Deduplicate by name; first-seen width wins.
  let mut seen : List (Name × Nat) := []
  for (n, w) in allVars do
    unless seen.any (fun (m, _) => m == n) do
      seen := seen ++ [(n, w)]
  let header := "(set-logic QF_BV)\n(set-info :status unsat)\n"
  let decls := seen.foldl
    (fun acc (n, w) =>
      acc ++ s!"(declare-const v_{n.toString.replace "." "_"} (_ BitVec {w}))\n")
    ""
  let hypAsserts := hyps.foldl
    (fun acc h => acc ++ s!"(assert {h.toSmt})\n")
    ""
  let goalAssert := s!"(assert (not {goal.toSmt}))\n"
  let footer := "(check-sat)\n(exit)\n"
  return header ++ decls ++ hypAsserts ++ goalAssert ++ footer

/-- Build the QF_LRA query exactly as `z3_check` builds it. CVC5 reads
the same SMT-LIB v2.6 format, so this is a thin re-export of
`Pythia.Z3Check.buildQuery` to keep the cvc5_check call sites
symmetric with the QF_BV path. -/
def buildQueryQF_LRA (hyps : List Pythia.Z3Check.SExpr)
    (goal : Pythia.Z3Check.SExpr) : String :=
  Pythia.Z3Check.buildQuery hyps goal

/-- Spawn CVC5 and read back its verdict. Lazy: only invoked at
tactic runtime, never at module load. The 5 second time limit
caps CI cost.

Implementation: write the SMT query to a temp file, then run
`cvc5 --tlimit 5000 --produce-models <file>`. We use a file
rather than stdin because the `takeStdin` API is awkward to thread
through `IO`, and the file path keeps things debuggable. -/
def runCvc5 (smt : String) : IO Pythia.Z3Check.Verdict := do
  let probe ← try
    IO.Process.output { cmd := "which", args := #["cvc5"] }
  catch _ =>
    return .notInstalled
  if probe.exitCode ≠ 0 then
    return .notInstalled
  let tmpDir ← IO.getEnv "TMPDIR" >>= fun
    | some d => pure d
    | none => pure "/tmp"
  let stamp ← IO.monoMsNow
  let tmpFile := s!"{tmpDir}/pythia_cvc5_check_{stamp}.smt2"
  IO.FS.writeFile tmpFile smt
  let result ← try
    IO.Process.output {
      cmd := "cvc5"
      args := #["--tlimit", "5000", "--produce-models", tmpFile]
    }
  catch e =>
    return .error s!"failed to invoke cvc5: {e}"
  let trimmed := result.stdout.trimAscii.toString
  if trimmed.startsWith "unsat" then
    return .unsat
  else if trimmed.startsWith "sat" then
    return .sat trimmed
  else if trimmed.startsWith "unknown" then
    return .unknown
  else
    return .error s!"cvc5 returned unexpected output: {trimmed} (stderr: {result.stderr.trimAscii.toString})"

end CVC5Check

open CVC5Check

/-! ### The `cvc5_check` tactic

Workflow:

  1. Read the main goal and its local context.
  2. Try the QF_BV encoder first (specific shape: `BitVec n`-typed
     atoms).
  3. If QF_BV encoding succeeds, ask CVC5 for `unsat`.
  4. Whether or not CVC5 was queried, ALWAYS try `bv_decide` as the
     actual proof.
  5. If the goal is not QF_BV, fall back to the QF_LRA encoder
     (shared with `z3_check`).
  6. If QF_LRA encoding succeeds, ask CVC5 for `unsat`.
  7. Whether or not CVC5 was queried, ALWAYS try `linarith` as the
     actual proof.
  8. If CVC5 said `unsat` but the reconstructor fails: fail loudly.
  9. If CVC5 was unavailable / out of fragment: fall through to the
     reconstructor directly. Worst case `cvc5_check ≡ bv_decide`
     (QF_BV) or `cvc5_check ≡ linarith` (QF_LRA).
 10. If CVC5 said `sat`: report the goal is unprovable in the
     fragment.
-/

/-- `cvc5_check` : Phase 2 cross-prover hammer for bit-vector and
linear-real-arithmetic goals. Tries the QF_BV path first; on a
non-bit-vector goal, falls back to QF_LRA. Asks CVC5 whether the
goal is valid in the appropriate logic, then reconstructs the
proof via `bv_decide` (QF_BV) or `linarith` (QF_LRA). CVC5's
verdict is never trusted in isolation: the Lean reconstructor
independently certifies the proof term against the kernel. -/
syntax (name := cvc5CheckTac) "cvc5_check" : tactic

@[tactic cvc5CheckTac] def evalCvc5Check : Tactic := fun stx => do
  match stx with
  | `(tactic| cvc5_check) =>
    let goal ← getMainGoal
    goal.withContext do
      let target ← goal.getType
      let target ← instantiateMVars target
      -- Coarse-shape dispatch: pick the bit-vector path when the goal's
      -- top-level relation is `BitVec`-typed, regardless of whether
      -- the operands sit inside the conservative QF_BV encoder. The
      -- encoder may give up on a corner of the operand syntax; we
      -- still want `bv_decide` reconstruction, not a misrouted
      -- `linarith` call.
      if (← goalLooksLikeBV target) then
        let lctx ← getLCtx
        let mut encHyps : List CVC5Check.BVExpr := []
        for ldecl in lctx do
          if ldecl.isImplementationDetail then continue
          let some h ← encodePropBV ldecl.type | continue
          encHyps := h :: encHyps
        let verdict : Pythia.Z3Check.Verdict ← match (← encodePropBV target) with
          | none => pure Pythia.Z3Check.Verdict.outOfFragment
          | some g =>
            let smt := buildQueryQF_BV encHyps g
            let v ← (runCvc5 smt : IO Pythia.Z3Check.Verdict)
            pure v
        let recRes ← try
          evalTactic (← `(tactic| bv_decide))
          pure (Except.ok ())
        catch e =>
          pure (Except.error e)
        match verdict, recRes with
        | .unsat, .ok _ => return ()
        | .unsat, .error _ =>
          throwError "cvc5_check: cvc5 reported `unsat` (QF_BV) but `bv_decide` could not reconstruct the proof. This is a soundness signal : refusing to close on cvc5's verdict alone."
        | .sat _, _ =>
          throwError "cvc5_check: cvc5 found a counterexample (sat) for a QF_BV goal. The goal is not valid."
        | .notInstalled, .ok _ => return ()
        | .notInstalled, .error _ =>
          throwError "cvc5_check: cvc5 binary not found on PATH (install via the upstream cvc5 release at https://cvc5.github.io/), and `bv_decide` could not close the QF_BV goal directly."
        | .unknown, .ok _ => return ()
        | .unknown, .error _ =>
          throwError "cvc5_check: cvc5 returned `unknown` for a QF_BV goal, and `bv_decide` could not close it directly."
        | .outOfFragment, .ok _ => return ()
        | .outOfFragment, .error _ =>
          throwError "cvc5_check: encoder reported out-of-fragment for a QF_BV goal, and `bv_decide` could not close it directly."
        | .error msg, .ok _ =>
          logInfo s!"cvc5_check: cvc5 invocation failed ({msg}); QF_BV proof closed by `bv_decide` fallback."
          return ()
        | .error msg, .error _ =>
          throwError "cvc5_check: cvc5 invocation failed ({msg}), and `bv_decide` could not close the QF_BV goal directly."
      else
        -- Not a bit-vector goal: fall to the QF_LRA path. The
        -- encoder is shared with `z3_check`.
        let encGoalLRA ← Pythia.Z3Check.encodeProp target
        let lctx ← getLCtx
        let mut encHyps : List Pythia.Z3Check.SExpr := []
        for ldecl in lctx do
          if ldecl.isImplementationDetail then continue
          let some h ← Pythia.Z3Check.encodeProp ldecl.type | continue
          encHyps := h :: encHyps
        let verdict : Pythia.Z3Check.Verdict ← match encGoalLRA with
          | none => pure Pythia.Z3Check.Verdict.outOfFragment
          | some g =>
            let smt := buildQueryQF_LRA encHyps g
            let v ← (runCvc5 smt : IO Pythia.Z3Check.Verdict)
            pure v
        let recRes ← try
          evalTactic (← `(tactic| linarith))
          pure (Except.ok ())
        catch e =>
          pure (Except.error e)
        match verdict, recRes with
        | .unsat, .ok _ => return ()
        | .unsat, .error _ =>
          throwError "cvc5_check: cvc5 reported `unsat` (QF_LRA) but `linarith` could not reconstruct the proof. This is a soundness signal : refusing to close on cvc5's verdict alone."
        | .sat _, _ =>
          throwError "cvc5_check: cvc5 found a counterexample (sat) for a QF_LRA goal. The goal is not valid."
        | .notInstalled, .ok _ => return ()
        | .notInstalled, .error _ =>
          throwError "cvc5_check: cvc5 binary not found on PATH (install via the upstream cvc5 release at https://cvc5.github.io/), and `linarith` could not close the QF_LRA goal directly."
        | .unknown, .ok _ => return ()
        | .unknown, .error _ =>
          throwError "cvc5_check: cvc5 returned `unknown` for a QF_LRA goal, and `linarith` could not close it directly."
        | .outOfFragment, .ok _ => return ()
        | .outOfFragment, .error _ =>
          throwError "cvc5_check: goal is outside the QF_BV / QF_LRA fragment, and `linarith` could not close it. (Phase 3 will route nonlinear goals.)"
        | .error msg, .ok _ =>
          logInfo s!"cvc5_check: cvc5 invocation failed ({msg}); QF_LRA proof closed by `linarith` fallback."
          return ()
        | .error msg, .error _ =>
          throwError "cvc5_check: cvc5 invocation failed ({msg}), and `linarith` could not close the QF_LRA goal directly."
  | _ => throwUnsupportedSyntax

end Pythia
