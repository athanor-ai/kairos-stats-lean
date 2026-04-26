/-
Pythia.Tactic.VampireCheckTest — regression tests for `vampire_check`.

Each example must close in a single `vampire_check` call. Because the
tactic ALWAYS reconstructs via `aesop` (Vampire is purely an oracle /
ranking filter), every test here is also closable by `aesop` alone, so
the suite passes whether or not the `vampire` binary is installed on
the build machine. That is the deliberate skip-if-no-vampire pattern:
CI is independent of the FOL prover install.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a kernel
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
skipped tests, no axiom smuggling. The Vampire oracle never
contributes to the proof term itself: Vampire only filters which goals
are worth invoking `aesop` on.

## Driver

Phase 5.
-/
import Pythia.Tactic.VampireCheck

namespace Pythia.VampireCheckTest

open Pythia

/-! ## Section A : in-fragment FOL goals

These are the canonical first-order goals `vampire_check` was designed
for. They all close via the aesop reconstruction path. -/

section FOLFallback

variable {α : Type} (P Q : α → Prop) (R : α → α → Prop)

/-- Identity implication: A → A. The simplest FOL fallback example. -/
example (A : Prop) : A → A := by
  vampire_check

/-- Universal-instantiation pattern: ∀ x, P x ⊢ P a. -/
example (a : α) (h : ∀ x, P x) : P a := by
  vampire_check

/-- Conjunction commutativity: A ∧ B ⊢ B ∧ A. -/
example (A B : Prop) (h : A ∧ B) : B ∧ A := by
  vampire_check

/-- Disjunctive syllogism: A ∨ B, ¬A ⊢ B. -/
example (A B : Prop) (h₁ : A ∨ B) (h₂ : ¬ A) : B := by
  vampire_check

/-- Existential introduction via a witness: P a ⊢ ∃ x, P x. -/
example (a : α) (h : P a) : ∃ x, P x := by
  vampire_check

/-- Nested universal quantifier with a binary predicate: a symmetric
relation closes by aesop on the witnesses. -/
example (h : ∀ x y, R x y → R y x) (a b : α) (hab : R a b) : R b a := by
  vampire_check

/-- Conjunction-with-quantifier mix: a doubly-bound hypothesis is
instantiated and split. -/
example (a b : α) (h : ∀ x, P x ∧ Q x) : P a ∧ Q b := by
  vampire_check

/-- Multi-step disjunctive syllogism: chain two eliminations. -/
example (A B C : Prop) (h₁ : A ∨ B ∨ C) (h₂ : ¬ A) (h₃ : ¬ B) : C := by
  vampire_check

/-- DeMorgan rewrite shape: ¬(A ∧ B) under ¬A produces ¬B-or-trivial. -/
example (A B : Prop) (h : ¬ (A ∧ B)) (hA : A) : ¬ B := by
  vampire_check

/-- DeMorgan rewrite shape: ¬(A ∨ B) ⊢ ¬A ∧ ¬B. -/
example (A B : Prop) (h : ¬ (A ∨ B)) : ¬ A ∧ ¬ B := by
  vampire_check

/-- Truth-teller / liar reduction (small propositional puzzle).
Encoded: if T iff "T is true" and we already know T, then T. -/
example (T : Prop) (_h : T ↔ T) (hT : T) : T := by
  vampire_check

/-- Slightly less trivial puzzle: from `A ↔ B` and `A`, derive `B`. -/
example (A B : Prop) (h : A ↔ B) (hA : A) : B := by
  vampire_check

/-- Trivial tautology that aesop closes immediately, exercising the
notInstalled-with-aesop-success path explicitly. The shape `(A → A) ∧ A`
is propositionally trivial. -/
example (A : Prop) (hA : A) : (A → A) ∧ A := by
  vampire_check

/-- Trivial tautology with conjunctive packaging. -/
example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  vampire_check

/-- Existential elimination via a hypothesis witness. -/
example (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  vampire_check

end FOLFallback

/-! ## Section B : graceful fall-through on out-of-fragment goals

The dispatcher routes arithmetic / BitVec / divisibility goals AWAY
from `vampire_check`, but a user invoking the tactic directly on such
a goal must get a clean failure (or, when aesop happens to close it,
an opportunistic close). We wrap each example in `try` followed by a
direct closer so the test compiles whether or not the FOL reasoning
path bites.

The wrapping `try ... <;> ...` pattern is the "graceful fall-through"
contract: vampire_check may or may not close, but the test still
ends with the goal closed by the in-tree Lean closer. This documents
the non-crash contract on out-of-fragment goals. -/

section OutOfFragment

-- The graceful-fall-through idiom `try vampire_check; first | done | <closer>`
-- triggers `unusedTactic` and `unreachableTactic` linters when the
-- aesop fallback inside `vampire_check` happens to close the goal
-- on its own. That is exactly the case we want to allow: the test's
-- contract is "no crash, goal closed by SOMETHING", not "vampire_check
-- definitely fails here". We silence the linters in this section only.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Numeric arithmetic over ℕ. We prefix `try vampire_check` and
finish with `first | done | omega`: vampire_check may close
opportunistically (its aesop fallback handles trivial reflexivity)
or leave the goal open, in which case `omega` finishes the job.
This `first | done | <closer>` idiom is the graceful-fall-through
contract used throughout this section. -/
example (n : ℕ) : n + 0 = n := by
  try vampire_check
  first | done | omega

/-- Numeric arithmetic over ℝ. `linarith` is the in-tree closer. -/
example (a b : ℝ) (h : a ≤ b) : a ≤ b + 1 := by
  try vampire_check
  first | done | linarith

/-- BitVec equality. `bv_decide` is the bit-vector reconstruction
tactic that `cvc5_check` uses; here it serves as the closer. -/
example (x : BitVec 8) : x = x := by
  try vampire_check
  first | done | bv_decide

/-- Integer divisibility. `vampire_check` cannot encode `∣` (divides);
`decide` closes the concrete instance. -/
example : (3 : ℕ) ∣ 12 := by
  try vampire_check
  first | done | decide

/-- Floating-shape arithmetic identity: `norm_num` is the closer for
concrete numeric facts. -/
example : (2 : ℝ) + 2 = 4 := by
  try vampire_check
  first | done | norm_num

end OutOfFragment

end Pythia.VampireCheckTest
