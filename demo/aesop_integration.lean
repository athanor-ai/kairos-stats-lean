/-
demo/aesop_integration.lean — worked examples for the "Mix with the standard
Lean toolkit" section of demo/README.md.

Every example closes with no `sorry`. Each block is annotated with the
dispatch path that actually closes the goal.
-/
import Pythia

namespace Pythia.Demo.AesopIntegration

open Pythia

/-!
## Pattern 1: pythia fallthrough to aesop

When no `@[stat_lemma]` rule matches, `pythia` falls through to the
`default` aesop ruleset. The goals below have nothing in the `Pythia`
ruleset; they close because Mathlib's bundled aesop lemmas cover them.
-/

/-- List append identity: no stat rule covers this; pythia falls through
    to aesop's default set, which closes it via `List.append_nil`. -/
example (l : List ℕ) : l ++ [] = l := by pythia

/-- Propositional tautology: again no stat rule applies; aesop closes it. -/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by pythia

/-- Nat successor: no stat rule covers this; pythia falls through to
    aesop/omega. -/
example (n : ℕ) : n + 1 > n := by pythia

/-!
## Pattern 2: pythia composed with linarith in a tactic block

Use `pythia` to reduce a goal to a simpler arithmetic residual, then
close the residual with `linarith`.  This is the recommended pattern
when `pythia` can normalise + partially discharge but the final step is
explicit arithmetic.
-/

/-- pythia handles nonneg cleanup; linarith closes the strict chain. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b ≤ 3) : a < 3 := by
  have hpos : 0 < a + b := by pythia
  linarith

/-- Register a concentration-style lemma, then mix pythia + linarith
    in a downstream proof. -/
@[stat_lemma]
theorem sq_nonneg_real (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

example (x : ℝ) (h : x ^ 2 ≤ 4) : x ^ 2 - 4 ≤ 0 := by
  have hnn : 0 ≤ x ^ 2 := by pythia   -- closed via @[stat_lemma]
  linarith

/-!
## Pattern 3: direct aesop (rule_sets := [Pythia]) usage

`@[stat_lemma]` is syntactic sugar for
`@[aesop safe apply (rule_sets := [Pythia])]`.
You can call the ruleset directly if you want aesop's full control
surface (timeout, tracing, depth) without the pythia dispatch layer.
-/

/-- Register a lemma manually, then close via the ruleset directly. -/
@[stat_lemma]
theorem sub_self_zero (x : ℝ) : x - x = 0 := sub_self x

/-- Direct ruleset call: finds and applies `sub_self_zero`. -/
example (y : ℝ) : y - y = 0 := by
  aesop (rule_sets := [Pythia])

/-- Direct ruleset call with config: same ruleset, explicit non-terminal
    warning suppressed so it composes cleanly inside larger tactic blocks. -/
example (z : ℝ) : z - z = 0 := by
  aesop (config := { warnOnNonterminal := false }) (rule_sets := [Pythia])

/-!
## Pattern 4: simp only [...] pre-processing, then pythia

Normalise the goal with a targeted `simp only` pass, then hand the
simplified form to `pythia`.  This avoids full `simp` blowing up the
goal while still benefiting from the pythia dispatch chain.
-/

/-- Normalise x * 1 to x with simp, then trivially close. -/
example (x : ℝ) : x * 1 + 0 = x := by
  simp only [mul_one, add_zero]
  pythia

/-- Normalise list membership after simp, then close with pythia. -/
example (n : ℕ) (h : n ≤ 4) : n + 0 ≤ 4 := by
  simp only [add_zero]
  pythia

end Pythia.Demo.AesopIntegration
