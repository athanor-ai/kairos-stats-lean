/-
Pythia.Tactic.FlagConcreteConstants — LLM-defense: parametricity guard.

## Problem

When LLMs specialize a general theorem to a single example (hard-coding
`n = 100`, `sigma = 0.5`, etc.), the customer gets a narrow statement
instead of the general result, without being told. The proof often compiles
cleanly, making the scope reduction invisible. This is a subtle hallucination:
the LLM "proves" the theorem for one concrete parameter rather than the
universally-quantified version the user intended.

## Solution: `#flag_concrete_constants`

A compile-time command that takes a theorem name `T`, walks the theorem
STATEMENT (its type, not its proof term), and reports every numeric literal
that appears as a fixed constant. This gives the user an immediate signal
that the statement has been concretized.

## How it works

1. Look up `T` via `getEnv` / `env.find?`.
2. Extract the statement via `ConstantInfo.type`.
3. Walk the type with a recursive accumulator, looking for:
   - `Expr.lit (.natVal n)` — raw Nat literal (kernel form).
   - `OfNat.ofNat _ (.lit (.natVal n)) _` — the front-end normal form
     for numeric literals in Lean 4 (detected via `Expr.nat?`).
4. Deduplicate and report each distinct value found.
5. On no constants: `logInfo "no fixed concrete numerical constants"`.
6. On constants found: `logInfo` with the list of values (NOT an error;
   the command is advisory, not blocking).

## What counts as "concrete"

Only numeric literals in the STATEMENT type are flagged. Universally
quantified variables, type parameters, and universe levels are not flagged.
The threshold is `>= 2`: the values 0 and 1 appear extremely frequently in
general statements (e.g. `0 < n`, `1 <= k`) and are rarely a sign of
over-specialization. Values >= 2 are flagged.

## API note

`Lean.Expr.forEach` requires `STWorld` / `MonadLiftT (ST omega) m` instances
not available in command-elaboration `Id` context. We implement a bespoke
recursive accumulator (`collectNatLits`) that folds over the expression tree
in a standard structural style. Visiting shared sub-terms multiple times is
safe for our purpose: we deduplicate the collected values before reporting.

## Soundness note

`#flag_concrete_constants` is purely informational. It emits `logInfo` only
and cannot block a correct compilation. The Lean kernel remains the sole
trusted checker.

## Driver

ATH-718 Layer 3, Phase 1. Part of the pythia LLM-defense suite.
-/
import Lean

namespace Pythia

open Lean Elab

/-- Extract a natural-number literal value from an expression, recognizing
both kernel form and front-end OfNat form:
- `Expr.lit (.natVal n)` — the raw kernel representation.
- `OfNat.ofNat _ (.lit (.natVal n)) _` — the Lean 4 normal form used in
  surface syntax (detected via `Expr.nat?`). -/
private def extractNatLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => e.nat?

/-- Recursively collect all natural-number literal values appearing in the
expression `e`. Descends into all sub-expressions. Duplicate values are
allowed in the output and should be deduplicated by the caller.

We walk manually (structural recursion) rather than via `Expr.forEach`
because the latter requires `STWorld` instances unavailable in pure `Id`. -/
partial def collectNatLits (e : Expr) : Array Nat :=
  go e #[]
where
  go (e : Expr) (acc : Array Nat) : Array Nat :=
    -- Check the node itself first.
    let acc' :=
      match extractNatLit? e with
      | some n => acc.push n
      | none   => acc
    -- Recurse into children.
    match e with
    | .app f a         => go a (go f acc')
    | .lam _ d b _     => go b (go d acc')
    | .forallE _ d b _ => go b (go d acc')
    | .letE _ t v b _  => go b (go v (go t acc'))
    | .mdata _ b       => go b acc'
    | .proj _ _ b      => go b acc'
    | _                => acc'

/-- `#flag_concrete_constants T` — walk the statement (type) of theorem `T`
and report every fixed numerical constant found.

A numerical constant here means a `Nat` literal with value `>= 2`. Constants
0 and 1 are ignored because they appear routinely in general statements
(e.g. `0 < n`, `1 <= k`).

On no constants found:
  `logInfo "no fixed concrete numerical constants"`

On constants found:
  `logInfo` listing the values (NOT an error; advisory only).

This command is an LLM-defense guard: run it on generated theorems to detect
over-specialization (hard-coded parameters that should be universally
quantified).

```lean
-- A general theorem -- should pass clean:
#flag_concrete_constants Pythia.ville_supermartingale_bound

-- An over-specialized theorem -- should report the hard-coded value:
-- theorem bad_tail (h : SubGaussian f 0.5) : P[f > 100] <= exp (-100) := ...
#flag_concrete_constants bad_tail
```
-/
elab "#flag_concrete_constants " name:ident : command => do
  let env ← getEnv
  let nm := name.getId
  -- Step 1: resolve the theorem name.
  match env.find? nm with
  | none =>
    logError m!"#flag_concrete_constants: '{nm}' is not found in the environment."
  | some ci =>
    -- Step 2: extract the theorem statement (type).
    let stmtType := ci.type
    -- Step 3: walk the type recursively, collecting numeric literals.
    let rawLits := collectNatLits stmtType
    -- Step 4: filter to values >= 2 and deduplicate.
    let flagged := rawLits.toList.filter (· >= 2) |>.eraseDups
    -- Step 5: report results.
    if flagged.isEmpty then
      logInfo m!"#flag_concrete_constants '{nm}': no fixed concrete numerical constants."
    else
      let valStr := flagged.map (fun n => s!"{n}") |> String.intercalate ", "
      logInfo m!"#flag_concrete_constants '{nm}': fixed numerical constant(s) found: {valStr}. \
        Check whether the theorem was over-specialized by an LLM. \
        Consider replacing each constant with a universally-quantified variable."

end Pythia
