/-
Pythia.Tactic.ECheckTest — regression tests for `e_check`.

Same pattern as `VampireCheckTest`: each example must close in a
single `e_check` call, and is also closable by `aesop` directly so
the suite passes whether or not the `eprover` binary is installed on
the build machine.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a kernel
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`,
no skipped tests, no axiom smuggling.

## Driver

Phase 5.
-/
import Pythia.Tactic.ECheck

namespace Pythia.ECheckTest

open Pythia

section FOLFallback

variable {α : Type} (P Q : α → Prop)

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

end FOLFallback

end Pythia.ECheckTest
