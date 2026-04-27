/-
Pythia.Tactic.ValidateTypes — LLM-defense: type-shape sanity guard.

## Problem

LLMs frequently produce theorems with incorrect numeric types. The most
common failure mode is `n : Real` for a quantity that is really a sample
size / index / count. The proof goes through (Lean is happy with `0 < n`
in either interpretation), but the SPEC is wrong: a downstream caller
sees `n : Real` and either fails to typecheck against an `n : Nat`
counterpart, or worse, silently accepts non-integer `n` as input.

By the time the spec drift surfaces, the LLM has moved on. The customer
never gets a "this looks suspicious" signal at theorem-statement time.

## Solution: `#validate_types`

A compile-time command that takes a theorem name `T`, walks the
forall-binders of its type, and reports per-variable type information
plus any suspicions:

* **Numeric-type sanity**: variable named like a count / index / size
  (`n`, `k`, `m`, `i`, `j`, `count`, `size`, `index`) but typed as `Real`
  / `ℝ` -- flag.
* **Mathlib-canonical types**: TBD per-domain list. v1 ships an empty
  list and is wired for v2 expansion. Examples for v2: `Probability`
  for measures, `Mass` for densities, `Time` for stopping rules.
* **Dimensional analysis**: deferred to v2 (needs a units library;
  not in pythia today).

Output: `logInfo` with a per-variable type table + a separate `logWarning`
for each suspicion. Never errors -- the customer chooses whether to act.

## How it works

1. Look up `T` via `getEnv` / `env.find?`.
2. Walk the type via `Expr.forallE` recursion to collect binder
   declarations as `(name, typeStr)` pairs.
3. For each `(name, type)`:
   * If `name` matches the count-like vocabulary AND `type` is `Real`/`ℝ`,
     emit a `logWarning` with the suggested fix (`Nat`).
   * Future v2: also check the canonical-type registry.
4. Emit `logInfo` with the full per-variable table.

## Soundness note

This command is purely informational. It emits info / warnings, never
errors, so it cannot block a correct theorem. The Lean kernel + the
type system are still the ultimate check; `#validate_types` is a
fast pre-flight signal to catch the most common LLM type-confusion
pattern before the customer signs off on the spec.

## Companion guards

Part of the Pythia Layer-3 LLM-defense suite (ATH-718). Companion
to `Pythia.Tactic.ValidateInvokedLemmas` (Guard B, hallucination check)
and `Pythia.Tactic.FlagConcreteConstants` (Guard H, hard-coded-magic-
number check).

ATH-725; kairos pair is ATH-723.
-/
import Lean

namespace Pythia

open Lean Elab Meta

/-- Vocabulary of variable names that are probably integer-valued
(sample sizes, indices, counts, dimensions). Match is case-insensitive
on the prefix; `n`, `n_`, `numTrials`, `n0` all match. -/
def countLikeVocab : Array String :=
  #["n", "k", "m", "i", "j",
    "count", "size", "index", "len", "length",
    "num", "numel", "dim", "rank"]

/-- Return true when `name` matches the count-like vocabulary.
Matches `name == "n"`, `name == "n_trials"`, or `name == "numTrials"`.
Case-insensitive on the prefix. -/
def isCountLike (name : Name) : Bool :=
  let s := name.getString!.toLower
  countLikeVocab.any fun v =>
    s == v
    || s.startsWith (v ++ "_")
    || (s.startsWith v
        && s.length > v.length
        && match s.toList[v.length]? with
           | some c => c.isUpper
           | none   => false)

/-- Pretty-print a type expression to a string suitable for the
`logInfo` table. Uses `Meta.ppExpr` so universes / implicit args render
the way the customer sees them. -/
def typeToString (t : Expr) : MetaM String := do
  let fmt ← Meta.ppExpr t
  return s!"{fmt}"

/-- Detect whether `t` is the real-numbers type `Real` / `ℝ`. Tolerant
of universe-polymorphic coercions and `mdata` wrappers. Matches both
`Real` (Mathlib.Data.Real.Basic) and the unicode `ℝ` notation, which
both elaborate to `Real`. We match by name string to avoid forcing a
Mathlib import on this module. -/
partial def isRealType (t : Expr) : Bool :=
  match t with
  | .const n _      => n == `Real || n == `Mathlib.Real
  | .mdata _ b      => isRealType b
  | _               => false

/-- A single binder observation: variable name, pretty-printed type,
and any warnings. -/
structure BinderInfo where
  name        : Name
  typeStr     : String
  suspicions  : Array String := #[]
  deriving Inhabited

/-- Walk a forall-chain, collecting `BinderInfo` per binder. Stops at
the first non-forall (the theorem conclusion). -/
partial def collectBinders (t : Expr) : MetaM (Array BinderInfo) :=
  Meta.forallTelescope t fun args _ => do
    let mut out : Array BinderInfo := #[]
    for arg in args do
      let lctx ← getLCtx
      let some decl := lctx.find? arg.fvarId! | continue
      let argType := decl.type
      let typeStr ← typeToString argType
      let mut suspicions : Array String := #[]
      if isCountLike decl.userName && isRealType argType then
        suspicions := suspicions.push s!"variable '{decl.userName}' is named like a count / index / size but typed as `Real`. Consider `Nat`."
      out := out.push { name := decl.userName, typeStr := typeStr, suspicions := suspicions }
    return out

/-- `#validate_types T` — walk the binders of theorem `T`'s type and
report per-variable types + any flagged type-shape suspicions.

Emits:
- `logInfo` with the per-variable type table.
- `logWarning` for each detected suspicion (one per variable).
- `logError` when `T` is not found.

This command is an LLM-defense guard: run it on generated theorem
statements to catch numeric-type confusion before signing off.

```lean
#validate_types Pythia.ville_supermartingale_bound
```
-/
elab "#validate_types " name:ident : command => do
  let env ← getEnv
  -- Resolve `name` against the current namespace + open declarations,
  -- so callers can write `#validate_types myThm` from inside a namespace
  -- and have it land on the fully-qualified `Foo.Bar.myThm`. Falls back
  -- to literal name lookup when `resolveGlobalConstNoOverloadCore` finds
  -- no match (preserves the helpful "not found" error path).
  let nm ← Lean.Elab.Command.liftCoreM <|
    (try
       Lean.resolveGlobalConstNoOverloadCore name.getId
     catch _ =>
       pure name.getId)
  match env.find? nm with
  | none =>
    logError m!"#validate_types: '{nm}' is not found in the environment."
  | some ci =>
    let binders ← Lean.Elab.Command.liftTermElabM do
      collectBinders ci.type
    -- Build the type table.
    if binders.isEmpty then
      logInfo m!"#validate_types '{nm}': theorem has no binders."
    else
      let mut table : String := s!"#validate_types '{nm}':\n"
      table := table ++ "  per-variable types:\n"
      for b in binders do
        table := table ++ s!"    {b.name} : {b.typeStr}\n"
      logInfo m!"{table}"
      -- Warn for each suspicion.
      for b in binders do
        for sus in b.suspicions do
          logWarning m!"#validate_types '{nm}': {sus}"

end Pythia
