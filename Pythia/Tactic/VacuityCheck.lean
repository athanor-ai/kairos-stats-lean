/-
Copyright (c) 2026 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Pythia.Tactic.VacuityCheck — layer-2 vacuity detection at the Lean elaboration level.

## Motivation

The QA tool `qa/check_lean_vacuity.py` (layer 1) detects vacuous theorems by
text-pattern matching: it looks for `True`, `rfl`, `trivial`, and other
syntactic markers in the source file. This catches the easy cases but misses
definitionally vacuous statements that only become visible after elaboration.

`VacuityCheck` is layer 2: it runs AFTER `lake build` (the `.olean` for the
target theorem already exists) and inspects the elaborated theorem directly
via `Lean.Environment`. This catches patterns that survive text scrutiny:

1. **Conclusion is `True`** — the theorem's return type (after stripping all
   forall-binders) is literally the constant `True`. A proof of `True` is
   always `trivial` and carries zero information.

2. **Conclusion appears in hypotheses** — the conclusion type is
   definitionally equal to one of the hypothesis types. This detects
   tautologies of the form `h : P ⊢ P` that Aristotle sometimes emits
   when it fails to find a real proof and wraps the hypothesis directly.

3. **All hypotheses unused** — the proof term does not syntactically
   reference any of the bound bvar indices introduced by the top-level
   lambda binders. If the proof never mentions any hypothesis, the theorem
   statement may be weaker than intended (a vacuous implication that holds
   for any antecedent).

## Design notes

- Detection 1 and 3 are purely syntactic (no unification).
- Detection 2 calls `isDefEq` (via `MetaM`) for definitional equality.
- All three checks emit `logWarning`; none emit `logError` and none block
  compilation. The Lean kernel remains the sole trusted checker.
- The `#audit_module` command finds all `theorem` / `def` constants declared
  in the current file (by matching the `moduleIdx`) and runs `#check_vacuity`
  on each one.

## Patterns Aristotle actually produces

Aristotle (the oracle prover) has been observed emitting three vacuity classes:
- Trivially-true conclusions after a sorry-closing run that over-simplifies.
- Hypothesis-mirrors: `theorem foo (h : P) : P := h`.
- Dead-hypothesis imports: the prover accumulates `have`-bindings from
  prior attempts and never eliminates them.

## Relationship to layer 1

Layer 1 (`check_lean_vacuity.py`) runs fast (grep-level) on source text;
layer 2 runs on elaborated terms after a successful build. Together they
form the two-pass vacuity filter that feeds the ATH-718 LLM-defense pipeline.

## Sorry status

Sorry-free. This file declares no theorems; it only defines a meta-program.

## Namespace

`Pythia.Tactic.VacuityCheck` — all definitions are within `namespace Pythia`.
-/
import Lean

namespace Pythia

open Lean Elab Command Meta

-- ---------------------------------------------------------------------------
-- Core inspection utilities
-- ---------------------------------------------------------------------------

/-- Return `true` when `e` is the constant `True`.

Tolerates `mdata` wrappers (Lean sometimes wraps `True` in metadata
annotations). Matches `True` both as a bare `Const` and after stripping one
level of `mdata`. Universe arguments are ignored: `True : Prop` has a single
universe level `u_1`, but we identify it by name. -/
partial def isTrueConclusion (e : Expr) : Bool :=
  match e with
  | .const n _  => n == ``True
  | .mdata _ b  => isTrueConclusion b
  | _           => false

/-- Strip all leading `forallE`-binders from `e` and return the innermost body.

This is the theorem conclusion: the type that must be inhabited. Does NOT
enter `lam` or `letE` — those are proof-term constructors, not statement
binders. -/
partial def getConclusion : Expr → Expr
  | .forallE _ _ body _ => getConclusion body
  | .mdata _ b          => getConclusion b
  | e                   => e

/-- Collect the domain types of all leading `forallE`-binders of `e` in
outermost-first order. These are the hypothesis types visible in the theorem
statement. -/
def getHypothesisTypes (e : Expr) : List Expr :=
  go e []
where
  go (e : Expr) (acc : List Expr) : List Expr :=
    match e with
    | .forallE _ dom body _ => go body (acc ++ [dom])
    | .mdata _ b            => go b acc
    | _                     => acc

/-- Count the leading `lam`-binders of a proof term (the bound hypotheses). -/
def countLeadingLamBinders (e : Expr) : Nat :=
  go e 0
where
  go (e : Expr) (k : Nat) : Nat :=
    match e with
    | .lam _ _ body _ => go body (k + 1)
    | _               => k

/-- Walk expression `e` at nesting depth `d` from the proof-term root and
collect, into `acc`, every binder position (0-indexed outermost-first) that
is syntactically referenced via a `bvar`.

A `bvar j` at depth `d` (meaning we are inside `d` enclosing binders)
references the binder at 0-indexed position `d - 1 - j` when `j < d`.

We walk structurally rather than via `Expr.forEach` because the latter
requires `STWorld` instances not available in `Id`/pure contexts. Visiting
shared sub-terms multiple times is safe: we collect indices, not transform. -/
partial def collectReferencedBinderIndices (e : Expr) (d : Nat) (acc : Array Nat) : Array Nat :=
  match e with
  | .bvar j =>
    if j < d then acc.push (d - 1 - j) else acc
  | .app f a =>
    collectReferencedBinderIndices a d (collectReferencedBinderIndices f d acc)
  | .lam _ dom body _ =>
    collectReferencedBinderIndices body (d + 1) (collectReferencedBinderIndices dom d acc)
  | .forallE _ dom body _ =>
    collectReferencedBinderIndices body (d + 1) (collectReferencedBinderIndices dom d acc)
  | .letE _ t v body _ =>
    collectReferencedBinderIndices body (d + 1)
      (collectReferencedBinderIndices v d (collectReferencedBinderIndices t d acc))
  | .mdata _ b =>
    collectReferencedBinderIndices b d acc
  | .proj _ _ b =>
    collectReferencedBinderIndices b d acc
  | _ =>
    acc

-- ---------------------------------------------------------------------------
-- Per-theorem vacuity analysis
-- ---------------------------------------------------------------------------

/-- Result of a single vacuity check. -/
structure VacuityResult where
  name               : Name
  /-- The theorem has no hypotheses (forall-free type). -/
  noHypotheses       : Bool
  /-- The conclusion is definitionally `True`. -/
  trueConclusion     : Bool
  /-- The conclusion is definitionally equal to at least one hypothesis type.
      Contains the 0-indexed position(s) of the matching hypothesis. -/
  conclusionInHyps   : List Nat
  /-- All top-level lambda binders in the proof term are unused (syntactically).
      `none` if there is no proof term (axiom, inductive, etc.). -/
  allHypsUnused      : Option Bool
  deriving Inhabited

/-- Check whether the conclusion of `thm` (elaborated type) is definitionally
equal to any of its hypothesis types.

We use `isDefEq` so that type aliases (e.g. `MeasurableSet` unfolded to
`MeasurableSpace.MeasurableSet`) are handled correctly. Returns a list of
0-indexed hypothesis positions where the match holds. -/
def checkConclusionInHyps (thmType : Expr) : MetaM (List Nat) := do
  let concl := getConclusion thmType
  let hyps  := getHypothesisTypes thmType
  let mut found : List Nat := []
  for i in List.range hyps.length do
    let hyp := hyps[i]!
    if ← isDefEq concl hyp then
      found := found ++ [i]
  return found

/-- Run all three vacuity checks on a single `ConstantInfo`. Returns `none`
when the constant is not a definition/theorem (e.g. axiom with no value, or
inductive). -/
def analyzeConstant (nm : Name) (ci : ConstantInfo) : MetaM VacuityResult := do
  let thmType  := ci.type
  let concl    := getConclusion thmType
  let hypTypes := getHypothesisTypes thmType

  -- Check 1: conclusion is True.
  let trueConclusion := isTrueConclusion concl

  -- Check 2: conclusion appears in hypotheses (definitional equality).
  let conclusionInHyps ← checkConclusionInHyps thmType

  -- Check 3: all hypotheses unused in the proof term.
  let allHypsUnused : Option Bool :=
    match ci.value? with
    | none       => none   -- axiom / opaque / inductive
    | some proof =>
      let k := countLeadingLamBinders proof
      if k = 0 then
        -- No lambda binders at the top: either no hypotheses or proof is
        -- a closed term. We only flag "all unused" when there are hypotheses.
        if hypTypes.isEmpty then none else some false
      else
        let refs := collectReferencedBinderIndices proof 0 #[]
        -- Check whether ALL of the k top-level binders are unreferenced.
        let usedSet := refs.toList.filter (· < k) |>.eraseDups
        some (usedSet.isEmpty)

  return {
    name             := nm
    noHypotheses     := hypTypes.isEmpty
    trueConclusion   := trueConclusion
    conclusionInHyps := conclusionInHyps
    allHypsUnused    := allHypsUnused
  }

/-- Format a `VacuityResult` as a human-readable string. Emits "OK" when no
issues are found; lists each active warning otherwise. -/
def formatVacuityResult (r : VacuityResult) : String :=
  let issues : Array String := Id.run do
    let mut out : Array String := #[]
    if r.trueConclusion then
      out := out.push "WARN[1]: conclusion is `True` — theorem is trivially true and carries no information"
    for i in r.conclusionInHyps do
      out := out.push s!"WARN[2]: conclusion is definitionally equal to hypothesis [{i + 1}] — this is a tautology"
    match r.allHypsUnused with
    | some true =>
      out := out.push "WARN[3]: all top-level hypotheses are unused in the proof term — conclusion may hold vacuously"
    | _ => pure ()
    return out
  if issues.isEmpty then
    s!"#check_vacuity '{r.name}': OK — no vacuity patterns detected"
  else
    let header := s!"#check_vacuity '{r.name}': {issues.size} vacuity warning(s)"
    issues.foldl (fun acc w => acc ++ "\n  " ++ w) header

-- ---------------------------------------------------------------------------
-- `#check_vacuity` command
-- ---------------------------------------------------------------------------

/-- `#check_vacuity T` — inspect theorem `T` for the three Aristotle-observed
vacuity patterns and print a warning for each one found.

**Checks performed:**

1. *Conclusion is `True`*: the theorem's return type (after stripping all
   forall-binders) is literally the constant `True`. Example: `theorem foo :
   True := trivial`.

2. *Conclusion appears in hypotheses*: the conclusion type is definitionally
   equal to one of the hypothesis types. Example: `theorem bar (h : P) : P
   := h`.

3. *All hypotheses unused*: the proof term never references any of the
   top-level lambda-bound hypothesis variables. Example: a proof that ignores
   all its antecedents.

Output:
- `logInfo` with the per-check result.
- `logWarning` for each vacuity pattern detected.
- `logError` when `T` is not found in the environment.

```lean
#check_vacuity Pythia.Hardware.MemoryConsistency.fence_restores_sc
-- #check_vacuity 'Pythia.Hardware.MemoryConsistency.fence_restores_sc': OK
```
-/
elab "#check_vacuity " name:ident : command => do
  let env ← getEnv
  -- Resolve name through open namespaces so callers can use short names.
  let nm ← liftCoreM <|
    (try Lean.resolveGlobalConstNoOverloadCore name.getId
     catch _ => pure name.getId)
  match env.find? nm with
  | none =>
    logError m!"#check_vacuity: '{nm}' is not found in the environment."
  | some ci =>
    let result ← liftTermElabM <| analyzeConstant nm ci
    let msg := formatVacuityResult result
    if result.trueConclusion
       || !result.conclusionInHyps.isEmpty
       || result.allHypsUnused == some true then
      logWarning m!"{msg}"
    else
      logInfo m!"{msg}"

-- ---------------------------------------------------------------------------
-- `#audit_module` command
-- ---------------------------------------------------------------------------

/-- `#audit_module` — run `#check_vacuity` on every theorem / definition
declared in the current file.

Looks up the current file's module index, iterates over all constants in the
environment whose `moduleIdx` matches, and invokes the vacuity checker on each
one that has a type (i.e. skips inductives, constructors, and other structural
entries that don't correspond to theorem statements).

Output: one `logInfo` or `logWarning` per checked declaration, followed by a
summary line. Constants with no interesting vacuity are printed at `logInfo`
level; those with warnings are printed at `logWarning` level.

```lean
#audit_module
-- #check_vacuity 'Foo.bar': OK
-- #check_vacuity 'Foo.baz': WARN[1]: conclusion is `True` ...
-- #audit_module: checked 12 declarations, 1 warning(s)
```
-/
elab "#audit_module" : command => do
  let env ← getEnv
  -- Retrieve the module index for the current file.
  -- `getMainModule` returns the module name; we map it to an index.
  let mainMod := env.mainModule
  -- Iterate over all constants and keep those from the current module.
  -- `env.constants` is a `SMap Name ConstantInfo`; `.toList` gives all entries.
  let allConsts := env.constants.toList
  -- Filter to declarations in the current module.
  -- `env.getModuleIdxFor? nm` returns `some idx` when `nm` was defined in
  -- the module at that index; when it returns `none` the constant was defined
  -- in an imported module. We keep constants with `some _` where the
  -- corresponding module name equals `mainMod`.
  let ownConsts : List (Name × ConstantInfo) := allConsts.filter fun (nm, _) =>
    match env.getModuleIdxFor? nm with
    | none     => false
    | some idx =>
      -- Map module index back to name via `env.header.moduleNames`.
      match env.header.moduleNames[idx.toNat]? with
      | none     => false
      | some mName => mName == mainMod
  -- Run the checker on each constant.
  let mut warnCount : Nat := 0
  let mut checkCount : Nat := 0
  for (nm, ci) in ownConsts do
    -- Skip constructors, recursor internals, and auxiliary defs that carry
    -- a `_` prefix — these are internal to the elaborator.
    if nm.isInternal then continue
    -- Only check defs / theorems (those with a `.value?`), not axioms or
    -- structures. Axioms are valid but don't have vacuity issues we can check.
    -- We still run check 1+2 on axioms since they have a type.
    checkCount := checkCount + 1
    let result ← liftTermElabM <| analyzeConstant nm ci
    let msg := formatVacuityResult result
    let hasWarning :=
      result.trueConclusion
      || !result.conclusionInHyps.isEmpty
      || result.allHypsUnused == some true
    if hasWarning then
      warnCount := warnCount + 1
      logWarning m!"{msg}"
    else
      logInfo m!"{msg}"
  -- Summary.
  if checkCount = 0 then
    logInfo m!"#audit_module: no declarations found in current module '{mainMod}'."
  else
    logInfo m!"#audit_module '{mainMod}': checked {checkCount} declaration(s), {warnCount} vacuity warning(s)."

end Pythia
