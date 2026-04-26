/-
Pythia.Tactic.PythiaTest — regression tests for the `pythia`
headline tactic.

Each example must close in a single `pythia` call. CI fails if any
example regresses, ensuring the tactic stays viable as a one-shot
domain hammer.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a kernel
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
skipped tests, no fake closures.
-/
import Pythia.Tactic.Pythia

namespace Pythia.PythiaTest

open Pythia

/-! ## Section A — `@[stat_lemma]` registration and dispatch -/

/-- Tagging a trivial lemma with `@[stat_lemma]` registers it into the
`Pythia` aesop ruleset. -/
@[stat_lemma]
theorem add_zero_real (x : ℝ) : x + 0 = x := by ring

/-- Pythia closes goals that match a registered `@[stat_lemma]`. -/
example (x : ℝ) : x + 0 = x := by pythia

/-- Composite use of a registered `@[stat_lemma]` after rewriting. -/
example (x y : ℝ) : (x + 0) + (y + 0) = x + y := by pythia

/-! ## Section B — Mathlib fall-through (no registered rule needed) -/

/-- Pythia falls through to `omega` for ℕ arithmetic. -/
example (n : ℕ) : n + 0 = n := by pythia

/-- Pythia falls through to `omega` for compound ℕ arithmetic. -/
example (n m : ℕ) : n + m = m + n := by pythia

/-- Pythia falls through to `linarith` for ℝ linear inequalities. -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by pythia

/-- Pythia falls through to `linarith` with multi-step chain. -/
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) : a ≤ d := by
  pythia

/-! ## Section C — `positivity` fall-through (nonneg cleanup) -/

/-- Pythia closes nonneg goals via positivity. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia

/-- Pythia closes product nonneg via positivity. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by pythia

/-- Pythia closes sqrt nonneg unconditionally via positivity. -/
example (x : ℝ) : 0 ≤ Real.sqrt x := by pythia

/-- Pythia closes squared-nonneg via positivity. -/
example (x : ℝ) : 0 ≤ x ^ 2 := by pythia

/-! ## Section D — `simp` fall-through for normalization -/

/-- Pythia normalizes ℝ identities via simp+ring. -/
example (x : ℝ) : x * 1 = x := by pythia

/-- Pythia handles addition cancellation via simp. -/
example (x : ℝ) : x - x = 0 := by pythia

/-- Pythia handles list identities. -/
example (l : List ℕ) : l ++ [] = l := by pythia

/-! ## Section E — Composite goals (multi-tactic chain) -/

/-- Composite: hypothesis-driven nonneg via positivity. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by pythia

/-- Composite: linear arithmetic inferring strict from non-strict. -/
example (a b : ℝ) (h : a + 1 ≤ b) : a < b := by pythia

/-- Composite: ring identity that simp normalizes. -/
example (x y : ℝ) : (x + y) - y = x := by pythia

/-! ## Section F — `#stat_lemmas` command (introspection) -/

-- The `#stat_lemmas` command works at command level.
#stat_lemmas

end Pythia.PythiaTest
