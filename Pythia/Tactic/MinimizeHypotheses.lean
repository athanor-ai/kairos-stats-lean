/-
Pythia.Tactic.MinimizeHypotheses — LLM-defense: unused-hypothesis guard.

## Problem

When LLMs generate Lean theorems, they sometimes include hypotheses that are
never used in the proof. These superfluous hypotheses weaken the theorem: a
statement with a smaller hypothesis set is strictly stronger (harder to satisfy
for the caller). An LLM might add a hypothesis like `(hf : Continuous f)` when
the proof only needs `(hf : Measurable f)`, or include `(_unused : True)` as a
placeholder never referenced in the proof body.

## Solution: `#minimize_hypotheses`

A compile-time command that takes a theorem name `T`, walks its proof term, and
checks for each top-level hypothesis whether its de Bruijn bvar index appears
anywhere in the proof term scope (including as a type argument to subsequent
binders). Each hypothesis is reported as USED or UNUSED.

## How it works

1. Look up `T` via `getEnv` / `env.find?`.
2. Extract the proof term via `ConstantInfo.value?`.
3. Count the leading `lam`-binders `k` (number of top-level hypotheses).
4. Walk the COMPLETE proof term with `collectUsedBinderIndices`, tracking
   nesting depth. Whenever `bvar j` is seen at depth `d`, it references the
   binder at position `d - 1 - j` (0-indexed from outermost). Indices
   outside `[0, k)` are ignored (they would refer to outer context).
5. Report each hypothesis as USED (its binder index appears) or UNUSED.
6. Cross-reference with the theorem's type (`forallE` binders) to recover
   user-facing binder names.

## De Bruijn index mapping

At nesting depth `d` (inside `d` lambda/forall/let binders from the root),
`bvar j` (with `j < d`) refers to the binder entered at depth `d - j`, i.e.,
binder position `d - 1 - j` in 0-indexed outermost-first order. This covers:
- References in the proof body (after all hypothesis binders).
- References in the domain types of subsequent hypothesis binders (e.g.,
  `fun (a : Nat) (hab : a < b) =>` where `a` appears in `hab`'s type).

By walking the FULL proof term (not just the body after stripping lambdas),
we correctly identify type-level uses of earlier binders.

## API note

`Lean.Expr.forEach` requires `STWorld` / `MonadLiftT (ST omega) m` instances
unavailable in the command-elaboration `Id` context. We implement a bespoke
recursive accumulator (`collectUsedBinderIndices`) that walks the expression
tree structurally with a depth counter. Visiting shared sub-terms multiple
times is safe: we collect indices, not transform the term.

## Soundness note

This command is purely informational. It emits `logInfo` only and cannot block
a correct compilation. The Lean kernel remains the sole trusted checker.

v1 limitation: syntactic bvar analysis only. Universe-level uses of a variable
(in sorts/levels) are not tracked because universe variables live in a separate
layer from `Expr.bvar`. In practice, such cases are rare.

## Driver

ATH-724 Guard C. Part of the pythia LLM-defense suite.
-/
import Lean

namespace Pythia

open Lean Elab

/-- Walk expression `e` at nesting depth `d` (from the root of the proof term)
and collect the 0-indexed binder positions (outermost = 0) of every binder
that is syntactically referenced. A `bvar j` at depth `d` with `j < d`
references binder position `d - 1 - j`.

We walk structurally rather than via `Expr.forEach` because the latter
requires `STWorld` instances unavailable in pure `Id`. -/
partial def collectUsedBinderIndices (e : Expr) (depth : Nat := 0) : Array Nat :=
  go e depth #[]
where
  go (e : Expr) (d : Nat) (acc : Array Nat) : Array Nat :=
    match e with
    | .bvar j =>
      -- j < d means this bvar refers to one of the `d` enclosing binders.
      -- The binder position (0 = outermost) is d - 1 - j.
      if j < d then acc.push (d - 1 - j) else acc
    | .app f a =>
      go a d (go f d acc)
    | .lam _ dom body _ =>
      -- Domain is evaluated at depth d; body is under one more binder.
      go body (d + 1) (go dom d acc)
    | .forallE _ dom body _ =>
      go body (d + 1) (go dom d acc)
    | .letE _ t v body _ =>
      -- Let-binding: type and value at depth d; body under one more binder.
      go body (d + 1) (go v d (go t d acc))
    | .mdata _ b =>
      go b d acc
    | .proj _ _ b =>
      go b d acc
    | _ =>
      acc

/-- Count the leading `lam`-binders of a proof term, collecting `(name, domain)`
pairs in outermost-first order. -/
def countLeadingLams (e : Expr) : Nat × List (Name × Expr) :=
  go e 0 []
where
  go (e : Expr) (k : Nat) (acc : List (Name × Expr)) : Nat × List (Name × Expr) :=
    match e with
    | .lam n dom body _ => go body (k + 1) (acc ++ [(n, dom)])
    | _                 => (k, acc)

/-- Strip leading `forallE`-binders from a type expression, collecting binder
names in outermost-first order. Used to recover user-facing hypothesis names
from the theorem statement when the proof term uses system-generated names. -/
def stripForalls (e : Expr) : List Name :=
  go e []
where
  go (e : Expr) (acc : List Name) : List Name :=
    match e with
    | .forallE n _ body _ => go body (acc ++ [n])
    | _                   => acc

/-- `#minimize_hypotheses T` — walk the proof term of theorem `T` and report
which top-level hypotheses are syntactically referenced (USED) or absent
(UNUSED) in the proof.

A hypothesis is USED if its de Bruijn bvar index appears anywhere in the proof
term, including as a type argument in the domain of a subsequent hypothesis
binder. For example, in `fun (a : Nat) (hab : 0 < a) => hab`, hypothesis `a`
is USED because it appears in the type of `hab`.

Output format:
```
#minimize_hypotheses MyTheorem
  HYPOTHESES (3 total):
    [1] mu [USED]
    [2] h_finite [UNUSED]
    [3] hf [USED]
  RESULT: 1 of 3 hypotheses unused.
```

If all hypotheses are used: `all N hypotheses used`.
If the theorem has no top-level hypotheses: reports that.

This command is an LLM-defense guard: run it on generated theorems to detect
superfluous hypotheses that weaken the theorem statement without contributing
to the proof.

```lean
#minimize_hypotheses Pythia.ville_supermartingale_bound
```
-/
elab "#minimize_hypotheses " name:ident : command => do
  let env ← getEnv
  let nm := name.getId
  -- Step 1: resolve the theorem name.
  match env.find? nm with
  | none =>
    logError m!"#minimize_hypotheses: '{nm}' is not found in the environment."
  | some ci =>
    -- Step 2: extract the proof term.
    match ci.value? with
    | none =>
      logError m!"#minimize_hypotheses: '{nm}' has no proof term \
        (axiom, inductive, or constructor?)."
    | some proofTerm =>
      -- Step 3: count leading lam-binders and collect their names.
      let (k, lamBinders) := countLeadingLams proofTerm
      -- Step 3b: collect user-facing names from the theorem type.
      let forallNames := stripForalls ci.type
      -- If there are no top-level lam-binders, the theorem has no hypotheses.
      if k = 0 then
        logInfo m!"#minimize_hypotheses '{nm}': no top-level hypotheses found."
      else
        -- Step 4: walk the COMPLETE proof term to find all referenced binder indices.
        -- This covers both the proof body and binder domain types (type-level uses).
        let allRefs := collectUsedBinderIndices proofTerm 0
        -- Keep only references into the top-level k binders (indices 0..k-1).
        let usedSet := allRefs.toList.filter (· < k) |>.eraseDups
        -- Step 5: build per-hypothesis report lines.
        let lines : Array String := (Array.range k).map (fun i =>
          let isUsed := usedSet.contains i
          -- Prefer the forallE binder name (user-facing); fall back to lam name.
          let bName : Name :=
            if i < forallNames.length then
              forallNames[i]!
            else
              (lamBinders[i]!).1
          let tag := if isUsed then "[USED]" else "[UNUSED]"
          s!"    [{i + 1}] {bName} {tag}")
        -- Count unused hypotheses.
        let unusedCount : Nat := (Array.range k).foldl (fun acc i =>
          if usedSet.contains i then acc else acc + 1) 0
        -- Step 6: assemble and emit the report.
        let header := s!"#minimize_hypotheses '{nm}'\n  HYPOTHESES ({k} total):"
        let bodyLines := lines.foldl (fun acc l => acc ++ "\n" ++ l) ""
        if unusedCount == 0 then
          logInfo m!"{header}{bodyLines}\n  RESULT: all {k} hypotheses used."
        else
          logInfo m!"{header}{bodyLines}\n  RESULT: {unusedCount} of {k} hypotheses unused."

end Pythia
