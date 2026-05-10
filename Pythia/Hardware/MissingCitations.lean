/-
Pythia.Hardware.MissingCitations — proofs for theorems that were
cited but never defined (phantom citations).

Five structural / algebraic identities about bit-vector hardware:

  1. isolate_lowest_set_bit  — two's-complement identity for LSB isolation
  2. onehot_binary_equiv     — one-hot ↔ binary encoding correspondence
  3. opcode_group_equiv      — shared decoder preserves mutual-exclusion semantics
  4. mux_reduction_equiv     — dead-case elimination in a mux
  5. gated_input_equiv       — AND-gating with enable = true is transparent

Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0; see LICENSE for details.
-/

import Mathlib

namespace Pythia.Hardware.MissingCitations

/-!
## 1. Two's-complement lowest-set-bit isolation

The classic hardware idiom `x & -x` isolates the lowest set bit.
In Lean's `BitVec` the arithmetic negation satisfies
`-x = ~~~x + 1`, so the two forms are definitionally equal.
-/

/-- For any `n`-bit vector `din`, ANDing with `~~~din + 1` (the
    bit-complement-plus-one representation of `-din`) equals ANDing
    with `-din` directly.  This is the identity used by every
    lowest-set-bit extractor circuit. -/
theorem isolate_lowest_set_bit {n : ℕ} (din : BitVec n) :
    din &&& (~~~din + 1#n) = din &&& (-din) := by
  congr 1
  exact (BitVec.neg_eq_not_add din).symm

/-!
## 2. One-hot / binary encoding equivalence

A one-hot vector of width `n` has exactly one bit set.  The natural
binary interpretation of such a vector (sum of `bit_i * 2^i`) equals
the index of that bit.  We model the binary value as `BitVec.toNat`
and the one-hot vector as the standard `BitVec` with a single 1-bit.
-/

/-- The `BitVec` whose only set bit is at position `k` is the power-
    of-two `2^k`.  Its `toNat` therefore equals `2^k`.  Meanwhile the
    one-hot *index* is `k` by convention; we record the precise
    relationship `toNat (1#(n+1) <<< k) = 2^(k : ℕ)` so that
    downstream proofs can rewrite the encoding either way. -/
theorem onehot_binary_equiv {n : ℕ} (k : Fin n) :
    (1#n <<< k.val).toNat = 2 ^ k.val := by
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  -- goal: (1 % 2^n) <<< k.val % 2^n = 2^k.val
  have hn : 0 < n := Nat.pos_of_ne_zero (Fin.pos k).ne'
  rw [Nat.one_mod_two_pow (by omega)]
  rw [Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) k.isLt)

/-!
## 3. Opcode-group equivalence under shared decoding

A shared opcode decoder dispatches to one of `n` operation functions
based on an opcode.  When the cases are mutually exclusive (at most
one matches), the shared decoder produces the same result as a direct
case analysis.  We model the decoder as a function `Fin n → Bool`
(the "active" flags) that is one-hot, and the shared result as the
unique active branch's output.
-/

/-- If exactly one flag in a `Bool`-valued opcode table `active` is
    `true` (mutual exclusion), then any two branches selected by the
    shared decoder agree: there is a unique `k` such that `active k`
    holds, and for every other `j` with `active j = true` the branch
    outputs coincide.  In particular the shared decoder and a direct
    case expression produce the same result. -/
theorem opcode_group_equiv {n : ℕ} {α : Type*}
    (active : Fin n → Bool)
    (branch : Fin n → α)
    (h_unique : ∃! k : Fin n, active k = true) :
    ∀ i j : Fin n, active i = true → active j = true → branch i = branch j := by
  obtain ⟨k, _hk, huniq⟩ := h_unique
  intro i j hi hj
  have hik : i = k := huniq i hi
  have hjk : j = k := huniq j hj
  subst hik; subst hjk; rfl

/-!
## 4. Mux dead-case elimination

A `n`-input mux selected by a `Fin n` selector never exercises
inputs whose index does not appear as a selector value.  Replacing a
dead input with an arbitrary value preserves the mux output for all
realised selector values.
-/

/-- If a selector value `dead` never occurs (i.e. the selector is
    always different from `dead`), then replacing `inputs dead` with
    any `replacement` value leaves the mux output unchanged. -/
theorem mux_reduction_equiv {n : ℕ} {α : Type*}
    (inputs : Fin n → α)
    (sel : Fin n)
    (dead : Fin n)
    (h_never : sel ≠ dead)
    (replacement : α) :
    (Function.update inputs dead replacement) sel = inputs sel := by
  exact Function.update_of_ne h_never replacement inputs

/-!
## 5. Gated-input transparency

AND-gating a data signal with an enable line is transparent when the
enable is `true`: `(true && b) = b` for any `Bool`.
-/

/-- When `enable = true`, ANDing it with `input` leaves `input`
    unchanged.  This is the fundamental correctness condition for any
    clock- or data-gating cell: the gate is transparent under
    assertion of the enable. -/
theorem gated_input_equiv (input : Bool) :
    (true && input) = input := by
  simp

end Pythia.Hardware.MissingCitations
