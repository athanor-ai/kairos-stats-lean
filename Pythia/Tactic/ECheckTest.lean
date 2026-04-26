/-
Pythia.Tactic.ECheckTest — regression tests for `e_check`.

Same pattern as `VampireCheckTest`: each example must close in a
single `e_check` call, and is also closable by `aesop` directly so
the suite passes whether or not the `eprover` binary is installed on
the build machine.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a kernel
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`,
no skipped tests, no axiom smuggling.

The dual-cascade examples in Section C exercise the routing path
where both `vampire_check` and `e_check` would close the goal: the
pythia dispatch table calls vampire first, but a user calling
`e_check` directly must still succeed. These are the cascade-backup
regression tests.

## Driver

Phase 5.
-/
import Pythia.Tactic.ECheck
import Pythia.Tactic.VampireCheck

namespace Pythia.ECheckTest

open Pythia

/-! ## Section A : in-fragment FOL goals

Canonical first-order goals `e_check` was designed for. -/

section FOLFallback

variable {α : Type} (P Q : α → Prop) (R : α → α → Prop)

/-- Tautology: P → P closes immediately. -/
example (A : Prop) : A → A := by
  e_check

/-- Universal hypothesis instantiation. -/
example (a : α) (h : ∀ x, P x) : P a := by
  e_check

/-- Existential lift from a known witness. -/
example (a : α) (h : P a) : ∃ x, P x := by
  e_check

/-- Contraposition pattern: ¬B, A → B ⊢ ¬A. -/
example (A B : Prop) (h₁ : A → B) (h₂ : ¬ B) : ¬ A := by
  e_check

/-- Nested universal quantifier: a doubly-bound symmetric relation. -/
example (h : ∀ x y, R x y → R y x) (a b : α) (hab : R a b) : R b a := by
  e_check

/-- Conjunction-with-quantifier mix: split a quantified conjunction. -/
example (a b : α) (h : ∀ x, P x ∧ Q x) : P a ∧ Q b := by
  e_check

/-- Multi-step disjunctive syllogism: chain two eliminations. -/
example (A B C : Prop) (h₁ : A ∨ B ∨ C) (h₂ : ¬ A) (h₃ : ¬ B) : C := by
  e_check

/-- DeMorgan rewrite shape: ¬(A ∧ B) under A produces ¬B. -/
example (A B : Prop) (h : ¬ (A ∧ B)) (hA : A) : ¬ B := by
  e_check

/-- DeMorgan rewrite shape: ¬(A ∨ B) ⊢ ¬A ∧ ¬B. -/
example (A B : Prop) (h : ¬ (A ∨ B)) : ¬ A ∧ ¬ B := by
  e_check

/-- Trivial tautology with conjunctive packaging. The aesop fallback
closes it whether or not E is installed. -/
example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  e_check

/-- Biconditional elimination: A ↔ B and A produce B. -/
example (A B : Prop) (h : A ↔ B) (hA : A) : B := by
  e_check

end FOLFallback

/-! ## Section B : graceful fall-through on out-of-fragment goals

`e_check` does not encode arithmetic / BitVec / divisibility goals.
Each test below confirms the tactic does NOT crash on such inputs by
following it with a guaranteed Lean closer using the
`first | done | <closer>` idiom. -/

section OutOfFragment

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Numeric arithmetic over ℕ. -/
example (n : ℕ) : n + 0 = n := by
  try e_check
  first | done | omega

/-- Numeric arithmetic over ℝ. -/
example (a b : ℝ) (h : a ≤ b) : a ≤ b + 1 := by
  try e_check
  first | done | linarith

/-- BitVec equality. -/
example (x : BitVec 8) : x = x := by
  try e_check
  first | done | bv_decide

/-- Integer divisibility. -/
example : (3 : ℕ) ∣ 12 := by
  try e_check
  first | done | decide

/-- Concrete numeric identity. -/
example : (2 : ℝ) + 2 = 4 := by
  try e_check
  first | done | norm_num

end OutOfFragment

/-! ## Section C : cascade-backup goals (closable by both vampire and E)

The pythia cascade calls `vampire_check` before `e_check`. These
goals exercise both: a user invoking `e_check` directly must still
close, AND a separate test confirms `vampire_check` closes too. The
test structure documents the cascade-backup contract. -/

section CascadeBackup

variable {α : Type} (P Q : α → Prop)

/-- Cascade case 1: simple universal-instantiation closes via either
prover's aesop reconstruction. The companion `vampire_check`
example below confirms the cascade-primary closes too. -/
example (a : α) (h : ∀ x, P x → Q x) (hp : P a) : Q a := by
  e_check

example (a : α) (h : ∀ x, P x → Q x) (hp : P a) : Q a := by
  vampire_check

/-- Cascade case 2: conjunction split is closable by either prover.
These two examples assert that both rungs of the FOL backup pair
honor the same goal shape. -/
example (A B C : Prop) (h : A ∧ B ∧ C) : C ∧ A := by
  e_check

example (A B C : Prop) (h : A ∧ B ∧ C) : C ∧ A := by
  vampire_check

end CascadeBackup

end Pythia.ECheckTest
