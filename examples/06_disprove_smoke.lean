/-
examples/06_disprove_smoke.lean — the `disprove` counterexample finder.

`disprove` is the dual of `z3_check`: where `z3_check` asks Z3 to refute
the negation of a goal (and on success Lean reconstructs the proof),
`disprove` asks Z3 to find a satisfying model for the negation. If
one exists, the goal is FALSE and Z3 hands back a concrete witness.

Lean has no built-in counterexample finder. `disprove` adds one by
adapting the same Z3 oracle infrastructure used by `z3_check`.

## How to run

Uncomment any `example` block below and elaborate the file. `disprove`
will throw an error reporting a concrete counterexample like:

```
disprove: counterexample found.
  x = 0.5
  y = 0
The goal is FALSE under these values.
```

The blocks are commented out so this file elaborates clean. Each one
is a known-false universal claim suitable for testing the witness
extraction path.

## Why this is more than a closure tactic

`pythia` closes TRUE statements. `disprove` reasons about FALSE ones.
Together they catch user-error in two directions: a mistyped lemma
you thought was true (caught by `disprove` finding a witness) and a
true lemma you don't know how to close (caught by `pythia`
succeeding in one tactic invocation).
-/
import Pythia.Tactic.Disprove

namespace Pythia.Examples.Disprove

-- Uncomment any of the following to see disprove report a witness.

-- /-- `∀ x y : ℝ, x ≤ y` is false. Witness: x = 1/2, y = 0. -/
-- example : ∀ x y : ℝ, x ≤ y := by disprove

-- /-- Subtracting from a non-negative does not preserve non-negativity.
--     Witness: x = 0, y = 1/2. -/
-- example : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → x - y ≥ 0 := by disprove

-- /-- A strict inequality chain doesn't compress by 1.
--     Witness: a = -1/2, b = 0, c = 1/2. -/
-- example : ∀ a b c : ℝ, a < b → b < c → a < b - 1 := by disprove

-- /-- TRUE statement: `disprove` reports `goal appears VALID`. -/
-- example : ∀ x : ℝ, x = x := by disprove

end Pythia.Examples.Disprove
