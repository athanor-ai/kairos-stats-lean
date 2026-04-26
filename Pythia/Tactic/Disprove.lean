/-
Pythia.Tactic.Disprove — counterexample-finder tactic
: the `disprove` tactic.

## What it does

`disprove` is the dual of `z3_check`. Given a goal that the user
suspects is FALSE, it asks Z3 (or, in a future phase, CVC5) to find
a model that satisfies the hypotheses while violating the goal. If
Z3 returns `sat`, `disprove` extracts the model and reports each
witness variable to the user via a structured error message.

Workflow:

  1. Encode the goal `G` and hypotheses `H₁, ..., Hₙ` into SMT-LIB.
  2. Build a query asking Z3 to find a model for
     `H₁ ∧ ... ∧ Hₙ ∧ ¬G`. If such a model exists, the goal is not
     a theorem under those hypotheses.
  3. Append `(get-model)` so Z3 prints the witness assignments.
  4. Parse `(define-fun v_x () Real <value>)` lines into a list of
     (Lean-name, value-string) pairs.
  5. Fail the proof attempt with `throwError`, displaying the
     witness assignments. The user inspects the witness; the proof
     does NOT close.

## Architectural principle: counterexamples are not certificates

Lean has no built-in counterexample finder, and `disprove` does NOT
attempt to close any goal. The reported witness is informational
only: there is no soundness obligation on the parser, no kernel term
constructed, and no axiom added. The tactic always FAILS the proof
attempt — successfully finding a witness is reported as a failure
because the goal it disproves is, in fact, false. The user reads the
witness and either reformulates the goal, negates it, or proves the
negation by hand (often via `simp_all; norm_num` or `decide` once a
concrete witness is in scope).

This dovetails with the `z3_check` discipline. Z3 is an oracle for
both directions: in `z3_check` it ranks goals as worth invoking
`linarith` on; in `disprove` it produces an inspectable witness. In
neither tactic does Z3's verdict cross the kernel boundary.

## Phase 1 scope

Supported goal shapes match `z3_check`: linear (in)equalities over
`ℝ`, hypotheses of the same shape over `ℝ`-typed locals. Anything
outside the conservative QF_LRA fragment trips a clear
`outOfFragment` error rather than silently succeeding.

Out of scope: nonlinear arithmetic, quantifiers, integer-typed
goals (Phase 2 will extend to QF_LIA / QF_NRA via the same probe).

## Z3 availability

Identical to `Z3Check`: Z3 is invoked at tactic runtime via
`IO.Process.output`, never at module load. The module compiles and
loads on machines without z3; the `notInstalled` verdict surfaces a
helpful `apt-get install z3` message at use site.

The companion test file `DisproveTest.lean` is structured so that
test compilation passes whether or not z3 is on the build machine:
each example is wrapped to swallow the `notInstalled` path while
still exercising the witness path when z3 IS available.

## Driver

Phase 1. Phase 2 swaps in CVC5 as an alternate backend behind the
same `Verdict` interface, and adds quantifier-aware probes for ∃
witnesses inside hypothesis assertions.
-/
import Mathlib
import Lean.Elab.Tactic
import Pythia.Tactic.Z3Check

namespace Pythia

open Lean Elab Meta Tactic

/-! ### SMT-LIB encoding (reused from Z3Check)

The `Z3Check.encodeProp` and `Z3Check.encodeReal` functions cover
exactly the linear-real fragment we need. We import them and add
only the new pieces: `buildSatQuery` (which adds `(get-model)`) and
`parseModel` (which extracts `(define-fun v_x () Real <val>)`
entries from Z3's response). -/

namespace Disprove

open Z3Check

/-- Build a self-contained SMT-LIB v2.6 sat query for a goal `G`
under hypotheses `Hs`. Asks Z3 to find a model for
`(and H₁ ... Hₙ (not G))` and to print that model on `sat`.

Note the difference from `Z3Check.buildQuery`: there we want
`unsat` on the negation, so we assert exactly the same body but
with `(set-info :status unsat)` and no `(get-model)`. Here we want
`sat` on the same body, plus the model. The asserted formula is
identical: it's the verdict semantics that flip. -/
def buildSatQuery (hyps : List SExpr) (goal : SExpr) : String := Id.run do
  let allVars := (goal :: hyps).flatMap SExpr.vars
  let uniqVars := allVars.eraseDups
  let header := "(set-logic QF_LRA)\n(set-info :status sat)\n(set-option :produce-models true)\n"
  let decls := uniqVars.foldl
    (fun acc n => acc ++ s!"(declare-const v_{n.toString.replace "." "_"} Real)\n")
    ""
  let hypAsserts := hyps.foldl
    (fun acc h => acc ++ s!"(assert {h.toSmt})\n")
    ""
  let goalAssert := s!"(assert (not {goal.toSmt}))\n"
  let footer := "(check-sat)\n(get-model)\n(exit)\n"
  return header ++ decls ++ hypAsserts ++ goalAssert ++ footer

/-- Strip the `v_` prefix that the encoder prepends to user-level
names, then unmangle `_` back into `.` (a best-effort inverse of
`Name.toString.replace "." "_"`). The result is a Lean `Name` that
matches the user's local hypothesis when one segment of the
original `Name`. For deeper-namespaced locals the inverse is
ambiguous, so we just return a single-segment `Name`. -/
def unmangleName (s : String) : Name :=
  let stripped : String :=
    if s.startsWith "v_" then (s.drop 2).toString else s
  Name.mkSimple stripped

/-- Crude SMT-LIB model parser. Z3 prints `sat` followed by a
model block of the shape:

    (
      (define-fun v_x () Real 0.5)
      (define-fun v_y () Real (- (/ 1 2)))
    )

We extract each `v_x` and the value sub-expression that follows the
sort token (`Real` / `Int` / `Bool`), up to the matching close-paren
of the `define-fun` form. Values are returned verbatim, with
surrounding whitespace trimmed, so the user sees exactly what Z3
produced (including arithmetic forms like `(- (/ 1.0 2.0))`). We
deliberately do NOT re-parse the value into a Lean numeric literal:
the witness is for human inspection, and re-parsing would add a
soundness surface that buys nothing because the witness never
crosses the kernel.

Implementation note: SMT-LIB values can contain nested
s-expressions, so we count parens to find the right boundary rather
than relying on a regex. -/
partial def parseModel (raw : String) : List (Name × String) := Id.run do
  -- Split on the literal "define-fun" marker to get one chunk per
  -- variable. The first chunk is the preamble (`sat`, opening
  -- paren, whitespace) and is dropped.
  let parts := raw.splitOn "define-fun"
  let entries := parts.tailD []
  let mut out : List (Name × String) := []
  for entry in entries do
    -- After "define-fun" Z3 emits ` <name> () <sort> <value>)`.
    let trimmed : String := entry.trimAsciiStart.toString
    -- Take the name token: characters up to the next whitespace.
    let nameChars := trimmed.toList.takeWhile (fun c => !c.isWhitespace)
    let nameStr := String.ofList nameChars
    let afterName := trimmed.toList.drop nameChars.length
    -- Drop over the `()` arity marker by skipping any prefix of
    -- whitespace and parens (the empty parameter list looks like
    -- `()` in SMT-LIB v2.6).
    let afterArity := afterName.dropWhile
      (fun c => c.isWhitespace || c == '(' || c == ')')
    -- Drop the sort token (one of `Real`, `Int`, `Bool`); we walk
    -- past contiguous non-whitespace.
    let afterSort := afterArity.dropWhile (fun c => !c.isWhitespace)
    -- Walk the remaining chars, count parens, and collect the
    -- value up to the close-paren that ends the define-fun form.
    let mut depth : Int := 0
    let mut value : List Char := []
    let mut started := false
    for c in afterSort do
      if !started then
        if c.isWhitespace then
          continue
        else
          started := true
      if c == '(' then
        depth := depth + 1
        value := c :: value
      else if c == ')' then
        if depth == 0 then
          break
        else
          depth := depth - 1
          value := c :: value
      else
        value := c :: value
    let valueStr : String := (String.ofList value.reverse).trimAscii.toString
    if nameStr.length > 0 && valueStr.length > 0 then
      out := (unmangleName nameStr, valueStr) :: out
  return out.reverse

/-- Optional helper to query Z3 with a model-producing query.
Reuses `Z3Check.runZ3`'s probe-first plumbing. The returned
`Verdict.sat` payload contains the full Z3 stdout including the
model block. -/
def runZ3Sat (smt : String) : IO Verdict :=
  Z3Check.runZ3 smt

end Disprove

open Disprove

/-! ### The `disprove` tactic

Workflow:

  1. Read the main goal and its local context.
  2. Encode goal + hypotheses via `Z3Check.encodeProp`.
  3. Build a sat query via `buildSatQuery` and shell out to Z3.
  4. Whatever the verdict, the tactic FAILS the proof attempt:
       * `sat`           — report the parsed witness.
       * `unsat`         — tell the user the goal looks valid; suggest `pythia`.
       * `unknown`       — Z3 gave up.
       * `notInstalled`  — z3 binary not on PATH.
       * `outOfFragment` — encoder hit a non-linear-real construct.
       * `error`         — generic Z3 failure.

  5. There is no path that closes the goal. By design: this tactic
     produces information for the user, not a kernel term. -/

/-- `disprove` — counterexample-finder for linear-arithmetic goals
over `ℝ`. Given a goal the user believes is FALSE under the local
hypotheses, asks Z3 for a sat model and reports the witness via an
informative error. The proof attempt always fails: this tactic
never closes goals, it only reveals counterexamples for inspection.

Pairs with `z3_check` (which expects unsat) and `pythia` (which
attempts a real proof). Use `disprove` when a goal will not close
and you suspect a typo or unstated hypothesis. -/
syntax (name := disproveTac) "disprove" : tactic

@[tactic disproveTac] def evalDisprove : Tactic := fun stx => do
  match stx with
  | `(tactic| disprove) =>
    let goal ← getMainGoal
    goal.withContext do
      let target ← goal.getType
      let target ← instantiateMVars target
      -- Encode goal.
      let encGoal ← Z3Check.encodeProp target
      -- Collect encodable hypotheses.
      let lctx ← getLCtx
      let mut encHyps : List Z3Check.SExpr := []
      for ldecl in lctx do
        if ldecl.isImplementationDetail then continue
        let some h ← Z3Check.encodeProp ldecl.type | continue
        encHyps := h :: encHyps
      -- Run Z3 only if the goal is in fragment.
      let verdict : Z3Check.Verdict ← match encGoal with
        | none => pure Z3Check.Verdict.outOfFragment
        | some g =>
          let smt := Disprove.buildSatQuery encHyps g
          let v ← (Disprove.runZ3Sat smt : IO Z3Check.Verdict)
          pure v
      -- Branch on verdict. Every branch fails the proof, but with
      -- different messages.
      match verdict with
      | .sat raw =>
        let witnesses := Disprove.parseModel raw
        let body :=
          witnesses.foldl
            (fun acc (n, v) => acc ++ s!"  {n} = {v}\n")
            ""
        if witnesses.isEmpty then
          throwError s!"disprove: Z3 reported sat but the model parser found no witnesses. Raw output:\n{raw}"
        else
          throwError s!"disprove: counterexample found.\n{body}The goal is FALSE under these values. To prove the negation, use `by simp_all; norm_num` or supply this witness."
      | .unsat =>
        throwError "disprove: goal appears VALID, Z3 found no counterexample. Try `pythia` to close it."
      | .unknown =>
        throwError "disprove: Z3 returned `unknown`. The goal may be outside QF_LRA decidability or have hit the 5s timeout. No witness available."
      | .notInstalled =>
        throwError "disprove: z3 binary not found on PATH. Install via `apt-get install z3`. Without z3, no counterexample search is possible."
      | .outOfFragment =>
        throwError "disprove: goal is outside the Phase 1 linear-real fragment. The encoder cannot translate it to QF_LRA, so Z3 was not invoked. (Phase 2 will extend to nonlinear and integer arithmetic.)"
      | .error msg =>
        throwError s!"disprove: Z3 invocation failed: {msg}"
  | _ => throwUnsupportedSyntax

end Pythia
