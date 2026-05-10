import Mathlib

-- Gray counter correctness for async FIFO pointers.
-- Gray code ensures only one bit changes per increment,
-- preventing metastability-induced multi-bit errors in CDC.

def grayEncode (n : ℕ) : ℕ := n ^^^ (n >>> 1)

/-
Gray encoding is injective (different values → different codes)
-/
theorem gray_encode_injective : Function.Injective grayEncode := by
  -- To show that grayEncode is injective, we can use the fact that the bitwise XOR operation is injective.
  have h_injective : ∀ n m : ℕ, grayEncode n = grayEncode m → n = m := by
    intro n m hnm
    have h_xor : ∀ i : ℕ, n.testBit i = m.testBit i := by
      -- We'll use induction on $i$ to show that the bits of $n$ and $m$ are equal.
      have h_ind : ∀ i, (∀ j > i, n.testBit j = m.testBit j) → n.testBit i = m.testBit i := by
        intro i hi; have := congr_arg ( fun x => x.testBit i ) hnm; simp +decide at this;
        unfold grayEncode at this; simp_all +decide [ Nat.testBit_xor ] ;
      intro i;
      contrapose! h_ind;
      have h_finite : Set.Finite {j | n.testBit j ≠ m.testBit j} := by
        have h_finite : ∃ k, ∀ j ≥ k, n.testBit j = false ∧ m.testBit j = false := by
          use Nat.log 2 n + Nat.log 2 m + 1;
          intro j hj; constructor <;> rw [ Nat.testBit_eq_false_of_lt ] <;> linarith [ Nat.lt_pow_of_log_lt one_lt_two ( by linarith : Nat.log 2 n < j ), Nat.lt_pow_of_log_lt one_lt_two ( by linarith : Nat.log 2 m < j ) ] ;
        exact Set.finite_iff_bddAbove.2 ⟨ h_finite.choose, fun j hj => not_lt.1 fun contra => hj <| by have := h_finite.choose_spec j contra.le; aesop ⟩;
      exact ⟨ Finset.max' ( h_finite.toFinset ) ⟨ i, h_finite.mem_toFinset.mpr h_ind ⟩, fun j hj => Classical.not_not.1 fun h => not_lt_of_ge ( Finset.le_max' _ _ <| h_finite.mem_toFinset.mpr h ) hj, h_finite.mem_toFinset.mp <| Finset.max'_mem _ _ ⟩
    exact Nat.eq_of_testBit_eq h_xor
  assumption

/-
Consecutive Gray values differ in exactly one bit position
(Hamming distance = 1), equivalently their XOR is a power of 2
-/
theorem gray_consecutive_hamming_one (n : ℕ) :
    (grayEncode n ^^^ grayEncode (n + 1)).isPowerOfTwo := by
  -- We need to show that the XOR of the Gray codes of n and n+1 is a power of 2.
  have h_xor : ∃ k, grayEncode n ^^^ grayEncode (n + 1) = 2 ^ k := by
    -- Let $m = n ^^^ (n+1)$, which has the form $2^{j+1}-1$ where $j$ is the position of the lowest 0-bit in $n$ that flips to 1 when $n$ is incremented to $n+1$.
    set m := n ^^^ (n + 1)
    have hm_form : ∃ j, m = 2^(j+1) - 1 := by
      -- The binary representation of `n ^^^ (n+1)` is a sequence of 1's followed by 0's. This is because adding 1 to `n` flips the lowest 0-bit and all lower 1-bits.
      have h_binary : ∃ j, (n ^^^ (n + 1)) = 2 ^ (j + 1) - 1 := by
        have h_flip : ∀ k, (n.testBit k) ≠ ((n + 1).testBit k) ↔ k < Nat.factorization (n + 1) 2 + 1 := by
          intro k;
          induction' k with k ih generalizing n <;> simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
          · cases Nat.mod_two_eq_zero_or_one n <;> simp +decide [ *, Nat.add_mod ];
          · specialize ih ( n / 2 ) ; simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
            rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ];
            · rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> norm_num [ Nat.dvd_add_right ];
            · rw [ show 2 * c + 1 + 1 = 2 * ( c + 1 ) by ring, Nat.factorization_mul ] <;> norm_num;
              constructor <;> intro <;> omega
        use Nat.factorization (n + 1) 2;
        refine' Nat.eq_of_testBit_eq _;
        intro i; specialize h_flip i; by_cases hi : i < Nat.factorization ( n + 1 ) 2 + 1 <;> simp_all +decide [ Nat.testBit_xor ] ;
      exact h_binary;
    -- Then grayEncode n ^^^ grayEncode (n+1) = grayEncode(n ^^^ (n+1)) = grayEncode(m).
    have h_gray_xor : grayEncode n ^^^ grayEncode (n + 1) = grayEncode m := by
      grind +locals;
    -- Since $m = 2^{j+1} - 1$, we have $grayEncode(m) = 2^j$.
    obtain ⟨j, hj⟩ := hm_form
    have h_gray_encode_m : grayEncode (2^(j+1) - 1) = 2^j := by
      unfold grayEncode;
      refine' Nat.eq_of_testBit_eq _;
      grind +splitImp;
    aesop;
  exact h_xor

/-
Gray encode of 0 is 0
-/
theorem gray_zero : grayEncode 0 = 0 := by
  native_decide +revert

/-
Gray encoding preserves ordering info (MSB matches)
-/
theorem gray_msb_preserved (n : ℕ) (k : ℕ) (h : n < 2^k) :
    grayEncode n < 2^k := by
  -- Since $n < 2^k$, every bit beyond the $k$-th bit in $n$ is zero. Therefore, when we XOR $n$ with $n >>> 1$, the resulting number will also have zeros in all positions beyond the $k$-th bit.
  have h_zero_bits : ∀ i ≥ k, (n ^^^ (n >>> 1)).testBit i = false := by
    intro i hi;
    rw [ Nat.testBit_xor ];
    rw [ Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt ];
    · rfl;
    · exact lt_of_le_of_lt ( Nat.shiftRight_le _ _ ) ( lt_of_lt_of_le h ( Nat.pow_le_pow_right ( by decide ) hi ) );
    · exact h.trans_le ( Nat.pow_le_pow_right ( by decide ) hi );
  exact Nat.lt_pow_two_of_testBit (grayEncode n) h_zero_bits