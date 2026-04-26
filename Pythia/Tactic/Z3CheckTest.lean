/-
Pythia.Tactic.Z3CheckTest — regression tests for `z3_check`.

Each example must close in a single `z3_check` call. Because the
tactic ALWAYS reconstructs via `linarith` (Z3 is purely an oracle /
ranking filter), every test here is also closable by `linarith`
alone — so the suite passes whether or not the `z3` binary is
installed on the build machine. That's the deliberate skip-if-no-z3
pattern: CI is independent of the SMT install.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a
kernel term against `{propext, Classical.choice, Quot.sound}`. No
`sorry`, no skipped tests, no axiom smuggling. The Z3 oracle never
contributes to the proof term itself — Z3 only filters which goals
are *worth* invoking `linarith` on.

## Driver

Phase 1.
-/
import Pythia.Tactic.Z3Check

namespace Pythia.Z3CheckTest

open Pythia

/-- Transitivity of `≤` on reals. The canonical linarith goal. -/
example {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  z3_check

/-- Reverse-transitivity `<`-version. -/
example {a b c : ℝ} (h₁ : a < b) (h₂ : b < c) : a < c := by
  z3_check

/-- Mixed strict / nonstrict chain. -/
example {a b c d : ℝ} (h₁ : a < b) (h₂ : b ≤ c) (h₃ : c < d) : a < d := by
  z3_check

end Pythia.Z3CheckTest
