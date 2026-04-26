/-
Pythia.Tactic.CVC5CheckTest : regression tests for `cvc5_check`.

Each example must close in a single `cvc5_check` call. Because the
tactic ALWAYS reconstructs via `bv_decide` (for QF_BV) or `linarith`
(for QF_LRA), every test here is also closable by the corresponding
Lean tactic alone, so the suite passes whether or not the `cvc5`
binary is installed on the build machine. That is the deliberate
skip-if-no-cvc5 pattern: CI is independent of the SMT install.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a
kernel term against `{propext, Classical.choice, Quot.sound}`. No
`sorry`, no skipped tests, no axiom smuggling. The CVC5 oracle never
contributes to the proof term itself : CVC5 only filters which goals
are worth invoking the reconstructor on.

## Driver

Phase 2.
-/
import Pythia.Tactic.CVC5Check

namespace Pythia.CVC5CheckTest

open Pythia

/-! ## Section A : QF_BV path (closed by `bv_decide`) -/

/-- Reflexivity of bit-vector equality at width 8. -/
example (x : BitVec 8) : x = x := by
  cvc5_check

/-- Commutativity of bit-vector addition at width 8. -/
example (x y : BitVec 8) : x + y = y + x := by
  cvc5_check

/-- Bit-vector self-XOR is zero at width 8. -/
example (x : BitVec 8) : x ^^^ x = 0 := by
  cvc5_check

/-- Bit-vector AND is idempotent at width 8. -/
example (x : BitVec 8) : x &&& x = x := by
  cvc5_check

/-! ## Section B : QF_LRA path (closed by `linarith`) -/

/-- Transitivity of `≤` on reals. The canonical linarith goal,
mirrored from `Z3CheckTest`. -/
example {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  cvc5_check

/-- Reverse-transitivity `<`-version. -/
example {a b c : ℝ} (h₁ : a < b) (h₂ : b < c) : a < c := by
  cvc5_check

/-- Mixed strict / nonstrict chain. -/
example {a b c d : ℝ} (h₁ : a < b) (h₂ : b ≤ c) (h₃ : c < d) : a < d := by
  cvc5_check

end Pythia.CVC5CheckTest
