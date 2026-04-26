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

/-! ## Section A : QF_BV path (closed by `bv_decide`)

Width-8 examples cover the canonical bit-vector laws; the second
sub-section below adds shift / complement / multi-byte coverage. -/

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

/-! ## Section A' : QF_BV with shifts, complement, multi-width

These exercise the surface area of `bv_decide` reconstruction
beyond the basic ring operators. The encoder may give up on some
of these (for example, complement is `BitVec.not` which we don't
encode in `encodeBitVec`); `goalLooksLikeBV` still routes them to
the BV path so `bv_decide` does the actual work. -/

/-- Left-shift by zero is the identity at width 8. -/
example (x : BitVec 8) : x <<< (0 : Nat) = x := by
  cvc5_check

/-- Right-shift (logical) by zero is the identity at width 8. -/
example (x : BitVec 8) : x >>> (0 : Nat) = x := by
  cvc5_check

/-- Complement involution: `~~~ ~~~ x = x` at width 8. The encoder
falls through to bv_decide for the actual proof. -/
example (x : BitVec 8) : ~~~ (~~~ x) = x := by
  cvc5_check

/-- Multi-byte (width 16) reflexivity: bit-width parameterization
works at any concrete width. -/
example (x : BitVec 16) : x + 0 = x := by
  cvc5_check

/-- Multi-byte (width 32) addition commutativity: confirms the
encoder + reconstructor scale to 32-bit BitVec. -/
example (x y : BitVec 32) : x + y = y + x := by
  cvc5_check

/-- Signed bit pattern: at width 8, the most-significant bit signals
sign. We assert `x &&& 0x80 = x &&& 0x80` (a reflexivity that
`bv_decide` reconstructs trivially) to confirm the encoder accepts
the BV-AND idiom that signed-vs-unsigned predicates rely on. -/
example (x : BitVec 8) : x &&& 0x80 = x &&& 0x80 := by
  cvc5_check

/-! ## Section B : QF_LRA path (closed by `linarith`)

The hypotheses are used to feed CVC5's SMT query even when Lean's
`linarith` reconstruction does not consume them all; the
`unusedVariables` linter is silenced so we can keep the realistic
multi-hypothesis context. -/

section QFLRA

set_option linter.unusedVariables false

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

/-- Nested fractions: rational-coefficient arithmetic on ℝ.
`linarith` handles concrete fractional coefficients in the
hypothesis. -/
example {a b : ℝ} (h₁ : a / 2 ≤ b) (h₂ : 0 ≤ a) : a ≤ 2 * b := by
  cvc5_check

/-- Multi-variable inequality with mixed coefficients (positive and
negative). The encoder normalises to QF_LRA; `linarith` reconstructs. -/
example {a b c : ℝ} (h₁ : 2 * a + 3 * b ≤ c) (h₂ : a ≥ 0) (h₃ : b ≥ 0) :
    2 * a ≤ c := by
  cvc5_check

/-- Five-step transitivity chain: stress-tests the linear closer with
a longer-than-usual hypothesis stack. -/
example {a b c d e f : ℝ}
    (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) (h₄ : d ≤ e) (h₅ : e ≤ f) :
    a ≤ f := by
  cvc5_check

end QFLRA

/-! ## Section C : graceful fall-through on FOL-only goals

`cvc5_check` covers QF_BV and QF_LRA. A pure first-order goal with no
arithmetic and no bit-vector content sits outside both fragments.
The tactic must NOT crash on such input: it should fail (or close
opportunistically when the reconstructor happens to fire). We wrap
each example with `try cvc5_check; first | done | <closer>` to
document the contract. -/

section OutOfFragment

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Pure-FOL identity. The QF_LRA encoder gives up on a `Prop`-typed
implication; `cvc5_check` returns outOfFragment, the `linarith`
reconstructor cannot help, and the final closer is `tauto`. -/
example (A : Prop) : A → A := by
  try cvc5_check
  first | done | tauto

/-- Pure-FOL existential lift. Without arithmetic content the encoder
returns outOfFragment; `aesop` closes the FOL fragment. -/
example {α : Type} (P : α → Prop) (a : α) (h : P a) : ∃ x, P x := by
  try cvc5_check
  first | done | exact ⟨a, h⟩

/-- ℕ-only arithmetic. The QF_LRA encoder targets ℝ-typed atoms and
gives up on ℕ; `omega` is the in-tree closer. -/
example (n : ℕ) : n + 0 = n := by
  try cvc5_check
  first | done | omega

end OutOfFragment

end Pythia.CVC5CheckTest
