/-
Pythia.Tactic.ValidateInvokedLemmas — LLM-defense: lemma-existence guard.

## Problem

When LLMs generate Lean tactic scripts, they frequently invoke lemma names
that do not exist in Mathlib or the current environment. For example, a
generated script might call `Mathlib.SubGaussian.tail_bound` when only
`MeasureTheory.SubGaussian.cgf_bound` exists. The error surfaces only
during a full `lake build` cycle, wasting the user's time.

## Solution: `#validate_invoked_lemmas`

A compile-time command that takes a theorem name `T`, walks every constant
reference in its proof term, and checks each against the environment. Any
name that is absent gets surfaced as a `logWarning` before the user attempts
a proof that depends on it.

## How it works

1. Look up `T` via `getEnv` / `env.find?`.
2. Extract the proof term via `ConstantInfo.value?`.
3. Walk the proof term recursively via `collectConsts`, accumulating every
   `Expr.const` name encountered.
4. For each collected name, verify `env.contains name`.
5. Report missing names via `logWarning`; report all-pass via `logInfo`.

## Soundness note

This command is purely informational. It emits warnings, never errors, so it
cannot block a correct proof. The Lean kernel is still the ultimate check;
`#validate_invoked_lemmas` is a fast pre-flight filter to catch the
most common LLM hallucination pattern before a full rebuild.

## API note

`Lean.Expr.forEach` requires `STWorld` / `MonadLiftT (ST ω) m` instances
that are not available in the command-elaboration `Id` context. We therefore
implement a bespoke recursive accumulator (`collectConsts`) that folds over
the expression tree in the standard structural style, without the caching
infrastructure of `ForEachExpr`. This is sound for our purpose: we are
collecting names, not transforming the term, so visiting shared sub-terms
multiple times is safe (names from duplicated sub-terms are deduped later).

## Driver

ATH-718 Layer 3, Phase 1. Part of the pythia LLM-defense suite.
-/
import Lean

namespace Pythia

open Lean Elab

/-- Recursively collect every `Expr.const` name appearing in `e`.
Returns the names in the order they are first encountered (pre-order DFS).
Shared sub-terms may be visited multiple times; dedup upstream if needed. -/
partial def collectConsts (e : Expr) : Array Name :=
  go e #[]
where
  go (e : Expr) (acc : Array Name) : Array Name :=
    match e with
    | .const n _       => acc.push n
    | .app f a         => go a (go f acc)
    | .lam _ d b _     => go b (go d acc)
    | .forallE _ d b _ => go b (go d acc)
    | .letE _ t v b _  => go b (go v (go t acc))
    | .mdata _ b       => go b acc
    | .proj _ _ b      => go b acc
    | _                => acc

/-- `#validate_invoked_lemmas T` — walk every `Expr.const` in the proof term
of theorem `T` and report any name that is absent from the current environment.

Emits:
- `logInfo  "all N invoked lemma(s) exist"` when every constant name is present.
- `logWarning` for each name that does not exist in the environment.
- `logError` when `T` itself is not found, or has no proof term (e.g. axioms,
  inductive types, constructors).

This command is an LLM-defense guard: run it on generated proofs to catch
hallucinated lemma names before attempting a full build.

```lean
#validate_invoked_lemmas Pythia.ville_supermartingale_bound
```
-/
elab "#validate_invoked_lemmas " name:ident : command => do
  let env ← getEnv
  let nm := name.getId
  -- Step 1: resolve the theorem name.
  match env.find? nm with
  | none =>
    logError m!"#validate_invoked_lemmas: '{nm}' is not found in the environment."
  | some ci =>
    -- Step 2: extract the proof term.
    match ci.value? with
    | none =>
      logError m!"#validate_invoked_lemmas: '{nm}' has no proof term (axiom, inductive, or constructor?)."
    | some proofTerm =>
      -- Step 3: collect all Expr.const names via recursive structural traversal.
      let allNames := collectConsts proofTerm
      -- Step 4: split into present and missing; deduplicate missing names.
      let presentCount := allNames.filter (env.contains ·) |>.size
      let missing := (allNames.filter (fun n => !env.contains n)).toList.eraseDups
      -- Step 5: report results.
      if missing.isEmpty then
        logInfo m!"#validate_invoked_lemmas '{nm}': all {presentCount} invoked lemma(s) exist."
      else
        for badName in missing do
          logWarning m!"#validate_invoked_lemmas '{nm}': unknown lemma '{badName}' \
            does not exist in the current environment. \
            (LLM hallucination guard: verify the correct Mathlib name.)"

end Pythia
