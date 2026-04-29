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
  exact (Nat.add_mod a b (2 ^ n))

/-- Multiplication mod 2^n distributes similarly. -/
theorem mul_mod_eq (n : ℕ) (a b : ℕ) :
    (a * b) % (2 ^ n) = ((a % (2 ^ n)) * (b % (2 ^ n))) % (2 ^ n) := by
  exact (Nat.mul_mod a b (2 ^ n))

/-! ## Overflow detection -/

/-
Unsigned overflow: a + b overflows n bits iff a + b ≥ 2^n.
-/
theorem unsigned_add_overflow_iff (n : ℕ) (a b : ℕ)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    2 ^ n ≤ a + b ↔ (a + b) % (2 ^ n) < a := by
  constructor <;> intro h;
  · rw [ Nat.mod_eq_sub_mod h ];
    rw [ Nat.mod_eq_of_lt ] <;> omega;
  · contrapose! h; rw [ Nat.mod_eq_of_lt ] <;> linarith;

/-! ## Sign extension -/

/-
Sign-extending a k-bit value to n bits (n ≥ k) preserves the
two's complement interpretation.
-/
theorem sign_extend_preserves_value (k n : ℕ) (hkn : k ≤ n) (v : ℕ)
    (hv : v < 2 ^ k) :
    let signed_k := if v < 2 ^ (k - 1) then (v : ℤ) else (v : ℤ) - (2 ^ k : ℤ)
    let extended := if v < 2 ^ (k - 1) then v else 2 ^ n - (2 ^ k - v)
    let signed_n := if extended < 2 ^ (n - 1) then (extended : ℤ) else (extended : ℤ) - (2 ^ n : ℤ)
    signed_k = signed_n := by
  rcases k with ( _ | k ) <;> rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
  split_ifs <;> try linarith;
  · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hkn ];
  · exact absurd ‹_› ( by rw [ tsub_lt_iff_left ] <;> linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hkn, Nat.sub_add_cancel ( by linarith : v ≤ 2 * 2 ^ k ) ] );
  · grind

/-! ## Arithmetic shift -/

/-- Arithmetic right shift by m equals floor division by 2^m for
non-negative values. -/
theorem arith_shift_right_eq_div (n m : ℕ) (v : ℕ) (hv : v < 2 ^ n) :
    v / (2 ^ m) = Nat.shiftRight v m := by
  exact (Nat.shiftRight_eq_div_pow v m).symm

/-! ## Gray code -/

/-- Binary-to-Gray conversion: XOR of value with its right-shift. -/
def toGray (v : ℕ) : ℕ := v ^^^ (v / 2)

/-
Adjacent Gray code values differ in exactly one bit position.
Fundamental property used in async FIFO pointer crossing.
-/
theorem gray_adjacent_hamming_one (v : ℕ) (n : ℕ) (hv : v < 2 ^ n - 1) :
    (Nat.bits (toGray v ^^^ toGray (v + 1))).count true = 1 := by
  -- By definition of Gray code, we know that `toGray v ^^^ toGray (v + 1)` is a power of 2.
  have h_power_of_two : ∃ m : ℕ, toGray v ^^^ toGray (v + 1) = 2 ^ m := by
    unfold toGray;
    induction' n with n ih generalizing v <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
    rcases Nat.even_or_odd' v with ⟨ k, rfl | rfl ⟩;
    · norm_num [ Nat.add_div ];
      -- By simplifying, we can see that the expression indeed equals 1.
      have h_simp : (2 * k ^^^ k) ^^^ (2 * k + 1 ^^^ k) = 1 := by
        have h_simp : (2 * k ^^^ k) ^^^ (2 * k + 1 ^^^ k) = (2 * k ^^^ (2 * k + 1)) ^^^ (k ^^^ k) := by
          grind;
        simp_all +decide [ Nat.xor_assoc ];
        rw [ show 2 * k + 1 = 2 * k ^^^ 1 from ?_ ];
        · rw [ ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor ];
        · norm_num [ Nat.xor ];
      exact ⟨ 0, h_simp ⟩;
    · norm_num [ Nat.add_div ];
      obtain ⟨ m, hm ⟩ := ih k ( by omega );
      use m + 1;
      convert congr_arg ( · <<< 1 ) hm using 1;
      · refine' Nat.eq_of_testBit_eq _;
        intro i; rcases i with ( _ | i ) <;> simp +decide [ Nat.testBit_xor, Nat.testBit_shiftLeft ] ;
        · norm_num [ Nat.add_mod, Nat.mul_mod, Nat.xor ];
          grind +splitImp;
        · simp +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
          norm_num [ Nat.add_div, Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
      · norm_num [ Nat.shiftLeft_eq, pow_succ' ];
        ring;
  obtain ⟨ m, hm ⟩ := h_power_of_two; rw [ hm ] ;
  exact Nat.recOn m ( by decide ) fun n ihn => by simp_all +decide [ Nat.pow_succ' ] ;

/-! ## Circular buffer (FIFO) -/

/-
The following two theorems were stated with ℕ subtraction, which is
   truncating (a - b = 0 when a < b).  This makes both statements false.

   Counterexample for fifo_empty_iff:
     n = 2, rd = 3, wr = 1 → rd % 4 = 3, wr % 4 = 1 (LHS false),
     (wr - rd) % 4 = (1 - 3) % 4 = 0 % 4 = 0 (RHS true).

   Counterexample for fifo_full_iff:
     n = 2, wr = 0, rd = 1 → (wr + 1) % 4 = 1 = rd % 4 (LHS true),
     (wr - rd) % 4 = 0 % 4 = 0 ≠ 3 (RHS false).

   We comment the originals out and supply corrected versions below
   that use ℤ subtraction instead.

theorem fifo_empty_iff (n : ℕ) (rd wr : ℕ) :
    rd % (2 ^ n) = wr % (2 ^ n) ↔ (wr - rd) % (2 ^ n) = 0 := by
  sorry

theorem fifo_full_iff (n : ℕ) (rd wr : ℕ) :
    (wr + 1) % (2 ^ n) = rd % (2 ^ n) ↔ (wr - rd) % (2 ^ n) = 2 ^ n - 1 := by
  sorry

Corrected FIFO empty condition using ℤ subtraction.
-/
theorem fifo_empty_iff (n : ℕ) (rd wr : ℕ) :
    rd % (2 ^ n) = wr % (2 ^ n) ↔ ((wr : ℤ) - (rd : ℤ)) % (2 ^ n : ℤ) = 0 := by
  zify;
  norm_num [ Int.emod_eq_emod_iff_emod_sub_eq_zero ];
  rw [ dvd_sub_comm ]

/-
Corrected FIFO full condition using ℤ subtraction.
-/
theorem fifo_full_iff (n : ℕ) (rd wr : ℕ) :
    (wr + 1) % (2 ^ n) = rd % (2 ^ n) ↔
      ((wr : ℤ) - (rd : ℤ)) % (2 ^ n : ℤ) = (2 ^ n : ℤ) - 1 := by
  constructor <;> intro h;
  · obtain ⟨ k, hk ⟩ := Nat.modEq_iff_dvd.mp h.symm;
    norm_num [ show ( wr : ℤ ) - rd = 2 ^ n * k - 1 by push_cast at hk; linarith ];
    norm_cast;
  · refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
    exact ⟨ ( wr - rd ) / 2 ^ n + 1, by push_cast; linarith [ Int.emod_add_mul_ediv ( wr - rd ) ( 2 ^ n ) ] ⟩

end Pythia.Hardware