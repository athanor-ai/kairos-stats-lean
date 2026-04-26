/-
examples/07_cross_prover_smoke.lean — the OSS cross-prover hammer chain.

Demonstrates pythia's four cross-prover oracles (`z3_check`,
`cvc5_check`, `vampire_check`, `e_check`), each routed by goal
shape. The examples below all close on machines without the prover
binary installed: each tactic falls through to a Lean-internal
reconstruction (`linarith` / `bv_decide` / `aesop`) so the smoke
tests pass in CI regardless.

When the binary IS installed, the oracle runs as a fast filter
ahead of the reconstruction step. The proof term Lean checks is
identical either way.
-/
import Pythia.Tactic.Z3Check
import Pythia.Tactic.CVC5Check
import Pythia.Tactic.VampireCheck
import Pythia.Tactic.ECheck

namespace Pythia.Examples.CrossProver

/-! ### z3_check: linear-real arithmetic. -/

example (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by z3_check
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by z3_check

/-! ### cvc5_check: bit-vector + linear-real backup. -/

example (x : BitVec 8) : x = x := by cvc5_check
example (x y : BitVec 16) : x + y = y + x := by cvc5_check
example (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by cvc5_check

/-! ### vampire_check / e_check: first-order logic. -/

example (P : α → Prop) (h : ∀ x, P x) (a : α) : P a := by vampire_check
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by e_check
example (P Q : Prop) : P ∧ Q → Q ∧ P := by vampire_check

end Pythia.Examples.CrossProver
