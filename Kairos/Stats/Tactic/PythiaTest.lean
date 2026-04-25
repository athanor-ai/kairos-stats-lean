/-
Kairos.Stats.Tactic.PythiaTest — smoke tests for the `pythia` tactic.

Iteration 1 verifies: tactic loads, attribute registers, ruleset is
queryable, and the tactic closes simple goals via the registered
ruleset + Mathlib fall-through.
-/
import Kairos.Stats.Tactic.Pythia

namespace Kairos.Stats.PythiaTest

/-- Tagging a trivial lemma with `@[stat_lemma]` registers it into the
`Kairos.Stats` aesop ruleset. -/
@[stat_lemma]
theorem add_zero_real (x : ℝ) : x + 0 = x := by ring

/-- Pythia closes goals that match a registered `@[stat_lemma]`. -/
example (x : ℝ) : x + 0 = x := by pythia

/-- Pythia falls through to Mathlib's standard automation when no kairos
rule applies. -/
example (n : ℕ) : n + 0 = n := by pythia

/-- Pythia handles compound goals via the cleanup chain. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia

-- The `#stat_lemmas` command works.
#stat_lemmas

end Kairos.Stats.PythiaTest
