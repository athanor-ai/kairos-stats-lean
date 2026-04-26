/-
Pythia.Tactic.TPTPEncode — shared TPTP encoder for the FOL oracle adapters.

## What it does

Encodes Lean `Expr`s and the active local context into TPTP (Thousands
of Problems for Theorem Provers) FOF format, the input dialect shared
by Vampire, E, and most other first-order superposition provers.

## Architectural principle: encoder is a fragment filter, not a proof step

The encoder is total but lossy. Every Lean expression that does not lie
in the pure-FOL-without-arithmetic fragment maps to `none`. The caller
(`vampire_check`, `e_check`) reads the `none` as a signal to skip the
external prover and fall through to `aesop` directly.

This keeps the soundness story simple: the kernel-checked Lean proof is
always built by `aesop` on the original goal. The TPTP query is only a
filter / ranking oracle, never a certificate. Same discipline as
`Z3Check`: oracle verdict gates whether `aesop` is invoked, but never
contributes to the proof term.

## Fragment

In:

  * `∀ x : T, P x`, `∃ x : T, P x` over uninterpreted (non-arithmetic)
    types `T`.
  * Propositional connectives: `And`, `Or`, `Not`, `Iff`, and the
    non-dependent arrow `P → Q`.
  * `Eq a b` over uninterpreted-type terms.
  * Uninterpreted predicates `P : T₁ → ... → Tₙ → Prop` and functions
    `f : T₁ → ... → Tₙ → T`.

Out (returns `none`):

  * Any subterm whose type is `ℝ`, `ℚ`, `ℤ`, `ℕ`, `Int`, `Nat`, `Rat`,
    or any other arithmetic carrier we recognise.
  * Arithmetic operators `HAdd.hAdd`, `HMul.hMul`, `HSub.hSub`, etc.
  * Order relations on numeric types (`LE.le` on `ℝ`, etc.).
  * Dependent products beyond simple non-dependent arrows.
  * Higher-order quantifiers, type-class projections.

The intent is conservative: when in doubt, return `none` and let
`aesop` close the goal (or fail honestly). Never produce a TPTP term
that lies about the Lean expression's meaning.

## Driver

Phase 5 of the cross-prover hammer. Shared between `VampireCheck` and
`ECheck`.
-/
import Mathlib
import Lean.Elab.Tactic

namespace Pythia
namespace TPTPEncode

open Lean Elab Meta

/-! ### TPTP AST

A small first-order syntax tree. Variables are quoted Lean local names;
constants and predicates are quoted Lean global names. Terms and
formulas are kept distinct so the encoder cannot accidentally place a
term where a formula is expected (or vice versa).

We render names to TPTP single-quoted-atom form: `'foo.bar'`. This
sidesteps every reserved-word / casing pitfall in the TPTP grammar
(predicate symbols must start lowercase, variables uppercase). Single-
quoted atoms are unrestricted. -/

/-- A first-order term: variable, constant, or applied function. -/
inductive TPTPTerm
  /-- A bound variable, identified by its Lean local name. Rendered to
  TPTP as `X_<hash>_<sanitised>` because TPTP variables must start
  with an uppercase letter. -/
  | var (name : Name)
  /-- A nullary constant or applied function symbol. Rendered as a
  single-quoted atom. -/
  | app (head : Name) (args : List TPTPTerm)
  deriving Inhabited

/-- A first-order formula. -/
inductive TPTPFormula
  | predApp (head : Name) (args : List TPTPTerm)
  | eq (a b : TPTPTerm)
  | top
  | bot
  | not (f : TPTPFormula)
  | and (a b : TPTPFormula)
  | or (a b : TPTPFormula)
  | imp (a b : TPTPFormula)
  | iff (a b : TPTPFormula)
  | all (boundName : Name) (body : TPTPFormula)
  | ex  (boundName : Name) (body : TPTPFormula)
  deriving Inhabited

/-! ### Pretty-printing -/

/-- TPTP variables must start with an uppercase ASCII letter. We map
each Lean local name to `X_<hash>_<sanitised>` where `<hash>` is a
stable digest of the Lean name. Different Lean locals get different
TPTP variables; identical Lean locals (same `Name`) collide
deterministically. -/
def varAtom (n : Name) : String :=
  let raw := n.toString.replace "." "_"
  let sanitised := raw.toList.filter (fun c => c.isAlphanum || c = '_')
  let suffix := String.ofList sanitised
  s!"X_{n.hash}_{suffix}"

/-- TPTP function / predicate symbols use single-quoted atoms so any
Lean name (with dots, primes, unicode, etc.) round-trips safely. -/
def symAtom (n : Name) : String :=
  let raw := n.toString
  -- Escape backslashes and single quotes inside the atom.
  let escaped := raw.replace "\\" "\\\\" |>.replace "'" "\\'"
  s!"'{escaped}'"

partial def TPTPTerm.toTPTP : TPTPTerm → String
  | .var n => varAtom n
  | .app head [] => symAtom head
  | .app head args =>
    let parts := args.map TPTPTerm.toTPTP
    s!"{symAtom head}({String.intercalate "," parts})"

partial def TPTPFormula.toTPTP : TPTPFormula → String
  | .predApp head [] => symAtom head
  | .predApp head args =>
    let parts := args.map TPTPTerm.toTPTP
    s!"{symAtom head}({String.intercalate "," parts})"
  | .eq a b => s!"({a.toTPTP} = {b.toTPTP})"
  | .top => "$true"
  | .bot => "$false"
  | .not f => s!"~({f.toTPTP})"
  | .and a b => s!"({a.toTPTP} & {b.toTPTP})"
  | .or  a b => s!"({a.toTPTP} | {b.toTPTP})"
  | .imp a b => s!"({a.toTPTP} => {b.toTPTP})"
  | .iff a b => s!"({a.toTPTP} <=> {b.toTPTP})"
  | .all n body => s!"(![{varAtom n}] : ({body.toTPTP}))"
  | .ex  n body => s!"(?[{varAtom n}] : ({body.toTPTP}))"

/-! ### Arithmetic-type detection

The encoder must reject any expression whose type is a numeric carrier.
We use a small allowlist of names we recognise as arithmetic. Anything
else is treated as an uninterpreted sort. The check is deliberately
syntactic, not type-class based, so we can run it cheaply inside the
encoder loop. -/

/-- Return `true` if the expression's head constant names a numeric
carrier we want to reject. Rejecting these shapes keeps the encoder
inside the pure-FOL-without-arithmetic fragment. -/
def isArithmeticType (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ =>
    n == ``Real || n == ``Rat || n == ``Int || n == ``Nat
      || n == ``ENNReal || n == ``NNReal || n == ``Complex
      || n == ``Float
  | _ => false

/-- Return `true` if the expression's head is an arithmetic operator
that puts the goal out of fragment. Used as an early reject inside the
formula and term walkers. -/
def isArithmeticOp (e : Expr) : Bool :=
  e.isAppOf ``HAdd.hAdd
    || e.isAppOf ``HSub.hSub
    || e.isAppOf ``HMul.hMul
    || e.isAppOf ``HDiv.hDiv
    || e.isAppOf ``HPow.hPow
    || e.isAppOf ``HMod.hMod
    || e.isAppOf ``Neg.neg

/-- Recognise the common ordering predicates. We reject these in the
formula walker before falling through to the predicate-application
case, because their first argument is the carrier type and any usable
shape is already covered by `z3_check` / `omega` / `linarith`. -/
def isOrderPredicate (e : Expr) : Bool :=
  e.isAppOf ``LE.le
    || e.isAppOf ``LT.lt
    || e.isAppOf ``GE.ge
    || e.isAppOf ``GT.gt

/-! ### Encoder core

Recursive descent on `Expr`. Two mutually recursive workers:

* `encodeTerm` — encodes a value-level expression as a `TPTPTerm`.
* `encodeFormula` — encodes a `Prop`-typed expression as a
  `TPTPFormula`.

Both return `none` on out-of-fragment input. Bound variables are
tracked by `userName` in a `NameSet`; if a free variable's user name
is in the set, it renders as a TPTP variable, otherwise as a constant. -/

abbrev BoundEnv := NameSet

mutual
  /-- Encode an expression as a TPTP term. Returns `none` on
  out-of-fragment input (arithmetic, dependent application, etc.). -/
  partial def encodeTerm (bound : BoundEnv) (e : Expr) :
      MetaM (Option TPTPTerm) := do
    let e ← instantiateMVars e
    let ty ← try inferType e catch _ => return none
    if isArithmeticType ty then return none
    if isArithmeticOp e then return none
    match e with
    | .fvar fv =>
      let decl ← fv.getDecl
      if bound.contains decl.userName then
        return some (.var decl.userName)
      else
        return some (.app decl.userName [])
    | .const n _ => return some (.app n [])
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let head ← match f with
        | .const n _ => pure n
        | .fvar fv => pure (← fv.getDecl).userName
        | _ => return none
      let mut encArgs : List TPTPTerm := []
      for a in args do
        -- Skip implicit-style arguments: type-formers and proof / instance arguments.
        if (← isType a) then continue
        if (← isProof a) then continue
        let aTy ← try inferType a catch _ => return none
        if isArithmeticType aTy then return none
        let some encA ← encodeTerm bound a | return none
        encArgs := encArgs ++ [encA]
      return some (.app head encArgs)
    | _ => return none

  /-- Encode a `Prop`-typed expression as a TPTP formula. Returns
  `none` on out-of-fragment input. -/
  partial def encodeFormula (bound : BoundEnv) (e : Expr) :
      MetaM (Option TPTPFormula) := do
    let e ← instantiateMVars e
    -- Recognise the propositional connectives by exact arity.
    if e.isAppOfArity ``True 0 then return some .top
    if e.isAppOfArity ``False 0 then return some .bot
    if e.isAppOfArity ``Not 1 then
      let some a' ← encodeFormula bound e.appArg! | return none
      return some (.not a')
    if e.isAppOfArity ``And 2 then
      let args := e.getAppArgs
      let some a' ← encodeFormula bound args[0]! | return none
      let some b' ← encodeFormula bound args[1]! | return none
      return some (.and a' b')
    if e.isAppOfArity ``Or 2 then
      let args := e.getAppArgs
      let some a' ← encodeFormula bound args[0]! | return none
      let some b' ← encodeFormula bound args[1]! | return none
      return some (.or a' b')
    if e.isAppOfArity ``Iff 2 then
      let args := e.getAppArgs
      let some a' ← encodeFormula bound args[0]! | return none
      let some b' ← encodeFormula bound args[1]! | return none
      return some (.iff a' b')
    if e.isAppOfArity ``Eq 3 then
      let args := e.getAppArgs
      let aTy := args[0]!
      if isArithmeticType aTy then return none
      let some a' ← encodeTerm bound args[1]! | return none
      let some b' ← encodeTerm bound args[2]! | return none
      return some (.eq a' b')
    -- Existential `∃ x : T, P x` is `Exists T (fun x => P x)`.
    if e.isAppOfArity ``Exists 2 then
      let args := e.getAppArgs
      let ty := args[0]!
      if isArithmeticType ty then return none
      match args[1]! with
      | .lam binderName bty body _ =>
        return ← withLocalDeclD binderName bty fun fv => do
          let body' := body.instantiate1 fv
          let userName := (← fv.fvarId!.getDecl).userName
          let bound' := bound.insert userName
          let some bf ← encodeFormula bound' body' | return none
          return some (.ex userName bf)
      | _ => return none
    -- Universal / arrow.
    match e with
    | .forallE binderName bty body _ =>
      if !body.hasLooseBVars then
        -- Non-dependent arrow `bty → body`. If `bty` is a proposition
        -- we treat this as implication; otherwise return none (would
        -- be a function-typed Prop, e.g. `α → Prop`, not in fragment).
        if (← isProp bty) then
          let some a' ← encodeFormula bound bty | return none
          let some b' ← encodeFormula bound body | return none
          return some (.imp a' b')
        else
          return none
      else
        if isArithmeticType bty then return none
        if (← isProp bty) then
          -- `(p : Prop) → q[p]`, which is a dependent quantifier over a
          -- proposition. Out of fragment.
          return none
        return ← withLocalDeclD binderName bty fun fv => do
          let body' := body.instantiate1 fv
          let userName := (← fv.fvarId!.getDecl).userName
          let bound' := bound.insert userName
          let some bf ← encodeFormula bound' body' | return none
          return some (.all userName bf)
    | _ =>
      -- Fall through: predicate application or arithmetic order
      -- relation. Reject the latter; encode the former.
      if isOrderPredicate e then return none
      let f := e.getAppFn
      let args := e.getAppArgs
      let head ← match f with
        | .const n _ => pure n
        | .fvar fv => pure (← fv.getDecl).userName
        | _ => return none
      let mut encArgs : List TPTPTerm := []
      for a in args do
        if (← isType a) then continue
        if (← isProof a) then continue
        let aTy ← try inferType a catch _ => return none
        if isArithmeticType aTy then return none
        let some encA ← encodeTerm bound a | return none
        encArgs := encArgs ++ [encA]
      return some (.predApp head encArgs)
end

/-- Public encoder entry-point. Maps a Lean `Prop` expression to a TPTP
formula, or `none` when the expression lies outside the supported
fragment. -/
def encodeFOL (e : Expr) : MetaM (Option TPTPFormula) :=
  encodeFormula {} e

/-! ### Query builder -/

/-- Emit a self-contained TPTP problem with `hyps` as axioms and `goal`
as the conjecture. Vampire and E both accept this dialect verbatim
(`fof(name, role, formula).`). -/
def buildQuery (hyps : List TPTPFormula) (goal : TPTPFormula) : String := Id.run do
  let mut out := ""
  let mut i := 0
  for h in hyps do
    out := out ++ s!"fof(h{i}, axiom, {h.toTPTP}).\n"
    i := i + 1
  out := out ++ s!"fof(goal, conjecture, {goal.toTPTP}).\n"
  return out

/-! ### Verdict -/

/-- Result of probing an FOL prover.

* `theorem` — prover refuted the negation; goal is provable in FOL.
* `counterSatisfiable` — prover found a counter-model; goal is not
  provable in FOL.
* `timeout` — prover hit its time limit without a verdict.
* `unknown` — prover gave up.
* `notInstalled` — binary not on `PATH`.
* `outOfFragment` — encoder returned `none`; we never invoked the prover.
* `error` — invocation failed for some other reason. -/
inductive Verdict
  | theorem
  | counterSatisfiable
  | timeout
  | unknown
  | notInstalled
  | outOfFragment
  | error (msg : String)
  deriving Inhabited

end TPTPEncode
end Pythia
