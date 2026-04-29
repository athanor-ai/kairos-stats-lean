/-
Pythia.Hardware.BitVec — hardware-specific bit-vector modular
arithmetic lemmas not yet in Mathlib's BitVec.

Every EBMC/CBMC property about a counter, ALU, or address decoder
chains through these. Mathlib has `BitVec` basics but the hardware
lemmas (carry propagation, sign extension, arithmetic shift =
floor-division, overflow detection) are sparse.
-/

import Mathlib

namespace Pythia.Hardware



/-! ## Modular arithmetic identities -/

/-- Addition mod 2^n distributes over mod: the classic hardware
identity that justifies ignoring high bits in an adder. -/
theorem add_mod_eq (n : ℕ) (a b : ℕ) :
    (a + b) % (2 ^ n) = ((a % (2 ^ n)) + (b % (2 ^ n))) % (2 ^ n) := by
  sorry

/-- Multiplication mod 2^n distributes similarly. -/
theorem mul_mod_eq (n : ℕ) (a b : ℕ) :
    (a * b) % (2 ^ n) = ((a % (2 ^ n)) * (b % (2 ^ n))) % (2 ^ n) := by
  sorry

/-! ## Overflow detection -/

/-- Unsigned overflow: a + b overflows n bits iff a + b ≥ 2^n. -/
theorem unsigned_add_overflow_iff (n : ℕ) (a b : ℕ)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    2 ^ n ≤ a + b ↔ (a + b) % (2 ^ n) < a := by
  sorry

/-! ## Sign extension -/

/-- Sign-extending a k-bit value to n bits (n ≥ k) preserves the
two's complement interpretation. -/
theorem sign_extend_preserves_value (k n : ℕ) (hkn : k ≤ n) (v : ℕ)
    (hv : v < 2 ^ k) :
    let signed_k := if v < 2 ^ (k - 1) then (v : ℤ) else (v : ℤ) - (2 ^ k : ℤ)
    let extended := if v < 2 ^ (k - 1) then v else 2 ^ n - (2 ^ k - v)
    let signed_n := if extended < 2 ^ (n - 1) then (extended : ℤ) else (extended : ℤ) - (2 ^ n : ℤ)
    signed_k = signed_n := by
  sorry

/-! ## Arithmetic shift -/

/-- Arithmetic right shift by m equals floor division by 2^m for
non-negative values. -/
theorem arith_shift_right_eq_div (n m : ℕ) (v : ℕ) (hv : v < 2 ^ n) :
    v / (2 ^ m) = Nat.shiftRight v m := by
  sorry

/-! ## Gray code -/

/-- Binary-to-Gray conversion: XOR of value with its right-shift. -/
def toGray (v : ℕ) : ℕ := v ^^^ (v / 2)

/-- Adjacent Gray code values differ in exactly one bit position.
Fundamental property used in async FIFO pointer crossing. -/
theorem gray_adjacent_hamming_one (v : ℕ) (n : ℕ) (hv : v < 2 ^ n - 1) :
    (Nat.bits (toGray v ^^^ toGray (v + 1))).count true = 1 := by
  sorry

/-! ## Circular buffer (FIFO) -/

/-- FIFO empty condition: read pointer equals write pointer mod 2^n. -/
theorem fifo_empty_iff (n : ℕ) (rd wr : ℕ) :
    rd % (2 ^ n) = wr % (2 ^ n) ↔ (wr - rd) % (2 ^ n) = 0 := by
  sorry

/-- FIFO full condition: write pointer is exactly one cycle ahead. -/
theorem fifo_full_iff (n : ℕ) (rd wr : ℕ) :
    (wr + 1) % (2 ^ n) = rd % (2 ^ n) ↔ (wr - rd) % (2 ^ n) = 2 ^ n - 1 := by
  sorry

end Pythia.Hardware
