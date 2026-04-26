/-
examples/01_pythia_smoke.lean — the headline `pythia` tactic.

Demonstrates the two ways `pythia` closes goals:

1. *Registered `@[stat_lemma]`*: a user-tagged theorem joins the
   `Pythia` aesop ruleset; `pythia` finds + applies it.
2. *Mathlib fall-through*: when no pythia rule matches, `pythia` falls
   through to `aesop` + a `simp/omega/linarith/positivity` cleanup
   chain.
-/
import Pythia.Tactic.Pythia

namespace Pythia.Examples.Smoke

open Pythia

/-- A user-tagged theorem registered via `@[stat_lemma]`. -/
@[stat_lemma]
theorem add_zero_real_smoke (x : ℝ) : x + 0 = x := by ring

/-- Pythia finds + applies the registered theorem. -/
example (x : ℝ) : x + 0 = x := by pythia

/-- Pythia falls through to Mathlib's standard automation when the
goal isn't covered by a pythia rule. -/
example (n : ℕ) : n + 0 = n := by pythia

/-- Pythia handles compound goals via the cleanup chain. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia

end Pythia.Examples.Smoke
