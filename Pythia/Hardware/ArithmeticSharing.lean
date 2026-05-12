/-
Copyright (c) 2026 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia Hardware Verification Team

Pythia.Hardware.ArithmeticSharing — formal verification of the arithmetic
sharing equivalences used in the production ALU gate-synthesis
optimization (-15.2% area reduction).

Gate synthesis rewrites SUB(a, b) as ADD(a, NOT(b) + 1), collapsing the
subtractor into the shared adder network.  This module provides
machine-checked proofs that constitute the third verification layer
alongside EBMC bounded model checking and yosys equivalence checking.

Four theorems are established:

  1. sub_eq_add_neg        — a - b = a + (-b)          (two's complement)
  2. neg_eq_not_add_one    — -b = ~~~b + 1              (NOT + 1 = negation)
  3. sub_eq_add_not_plus_one — a - b = a + ~~~b + 1     (full sharing identity)
  4. mask_merge_equiv       — (a & mask) | (b & ~~~mask)
                              = b ^^^ ((a ^^^ b) & mask)  (ALU mask-merge opt.)

All proofs are zero-sorry and work for any bit-width n.
-/

import Mathlib

namespace Pythia.Hardware.ArithmeticSharing

variable {n : ℕ} (a b mask : BitVec n)

/-! ## Theorem 1 — two's complement: subtraction is addition of negation -/

/-- `a - b = a + (-b)` for any `BitVec n`.
    This is the foundational two's complement identity: the hardware
    subtractor is literally an adder whose second operand is negated. -/
theorem sub_eq_add_neg : a - b = a + (-b) :=
  BitVec.sub_eq_add_neg a b

/-! ## Theorem 2 — negation is bitwise NOT plus one -/

/-- `-b = ~~~b + 1` for any `BitVec n`.
    Bitwise NOT flips every bit; adding 1 completes the two's complement
    negation.  This is the gate-level implementation that the synthesis
    tool exploits to share the incrementer between NEG and SUB paths. -/
theorem neg_eq_not_add_one : -b = ~~~b + 1#n :=
  BitVec.neg_eq_not_add b

/-! ## Theorem 3 — full arithmetic sharing identity -/

/-- `a - b = a + ~~~b + 1` for any `BitVec n`.
    Combines the two preceding lemmas.  This is the exact rewrite the
    AP_ALU_US gate-synthesis pass applies:
      SUB(a, b)  →  ADD(a, NOT(b), cin = 1)
    sharing the adder carry chain with the ADD instruction at the cost of
    only a mux on the carry-in and the B-side inversion. -/
theorem sub_eq_add_not_plus_one : a - b = a + ~~~b + 1#n := by
  rw [sub_eq_add_neg, neg_eq_not_add_one]
  rw [BitVec.add_assoc]

/-! ## Theorem 4 — mask-merge bitwise optimization -/

/-- `(a &&& mask) ||| (b &&& ~~~mask) = b ^^^ ((a ^^^ b) &&& mask)` for any `BitVec n`.
    This identity lets the ALU sharing network merge two masked values
    using only XOR and AND, avoiding an OR gate on the critical path.
    The synthesis tool applies it when the mask selects bits from `a` and
    the complement selects bits from `b`.

    Proof strategy: reduce to a pointwise Boolean identity and discharge
    with `bv_omega`. -/
theorem mask_merge_equiv :
    (a &&& mask) ||| (b &&& ~~~mask) = b ^^^ ((a ^^^ b) &&& mask) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not,
             BitVec.getElem_xor]
  cases a[i]
  · cases b[i]
    · cases mask[i] <;> simp
    · cases mask[i] <;> simp
  · cases b[i]
    · cases mask[i] <;> simp
    · cases mask[i] <;> simp

end Pythia.Hardware.ArithmeticSharing
