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

section FOLFallback

variable {α : Type} (P Q : α → Prop)

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

end FOLFallback

end Pythia.VampireCheckTest
