/-
Pythia.Hardware.ECC — Hamming distance error detection/correction
guarantees for linear codes.

Every ASIC memory controller relies on this: a (n, k, d) linear
code with minimum distance d detects all ≤(d-1)-bit errors and
corrects all ≤⌊(d-1)/2⌋-bit errors. Standard coding theory but
not in Mathlib or any Lean4 ecosystem library.

Aristotle target.
-/

import Mathlib

namespace Pythia.Hardware

/-- Hamming weight: number of 1-bits in a natural number. -/
noncomputable def hammingWeight (x : ℕ) : ℕ := (Nat.bits x).count true

/-- Hamming distance between two values. -/
noncomputable def hammingDist (x y : ℕ) : ℕ := hammingWeight (x ^^^ y)

/-
Hamming distance is a metric: triangle inequality.
-/
theorem hamming_triangle (x y z : ℕ) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  -- By definition of Hamming distance, we have:
  unfold hammingDist;
  -- Using the identity $(x ^^^ y) ^^^ (y ^^^ z) = x ^^^ z$, we can simplify the expression.
  have h_identity : (x ^^^ y) ^^^ (y ^^^ z) = x ^^^ z := by
    grind
  rw [← h_identity];
  -- By definition of Hamming weight, we know that
  have h_hamming_weight : ∀ (a b : ℕ), (Nat.bits (a ^^^ b)).count true ≤ (Nat.bits a).count true + (Nat.bits b).count true := by
    intro a b; induction' a using Nat.binaryRec with a ih generalizing b <;> induction' b using Nat.binaryRec with b ih' <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod ] ;
    cases a <;> cases b <;> simp_all +decide [ Nat.bit ];
    · -- By definition of multiplication by 2, the binary representation of $2 * n$ is just the binary representation of $n$ shifted left by one position.
      have h_shift : ∀ n : ℕ, (Nat.bits (2 * n)).count true = (Nat.bits n).count true := by
        intro n; induction n <;> simp_all +decide [ Nat.mul_succ, Nat.pow_succ' ] ;
        norm_num [ show 2 * _ + 2 = 2 * ( _ + 1 ) by ring, Nat.mul_mod, Nat.mul_div_assoc ];
      aesop;
    · rename_i h₁ h₂; specialize h₁ ih'; simp_all +decide [ ← add_assoc ] ;
      cases ih <;> simp_all +decide [ Nat.mul_mod, Nat.mul_div_assoc ];
    · rename_i h₁ h₂; specialize h₁ ih'; simp_all +arith +decide [ Nat.add_mod, Nat.mul_mod ] ;
      cases ih' <;> simp_all +decide [ Nat.mul_mod, Nat.mul_div_assoc ];
    · cases h : ih ^^^ ih' <;> simp_all +decide [ Nat.mul_mod, Nat.mul_div_assoc ];
      grind;
  exact h_hamming_weight _ _

/-
Hamming distance is symmetric.
-/
theorem hamming_symm (x y : ℕ) :
    hammingDist x y = hammingDist y x := by
  exact congr_arg _ ( Nat.xor_comm _ _ )

/-
A code with minimum distance d detects all error patterns of
weight ≤ d - 1. No valid codeword is within d-1 of another, so
any perturbation of weight < d lands outside the codebook.
-/
theorem detection_capacity
    (codewords : Finset ℕ)
    (d : ℕ) (hd : 2 ≤ d)
    (h_min_dist : ∀ c₁ ∈ codewords, ∀ c₂ ∈ codewords,
      c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (c : ℕ) (hc : c ∈ codewords)
    (e : ℕ) (he : 0 < hammingWeight e) (he_small : hammingWeight e ≤ d - 1) :
    c ^^^ e ∉ codewords := by
  -- By contradiction, assume $c \oplus e \in \text{codewords}$.
  by_contra h_contra
  have h_dist : hammingDist c (c ^^^ e) ≤ d - 1 := by
    unfold hammingDist; aesop;
  have h_dist_ge : d ≤ hammingDist c (c ^^^ e) := by
    apply h_min_dist c hc (c ^^^ e) h_contra; simp [he.ne'];
    cases e <;> simp_all +decide [ Nat.xor ];
    exact fun h => by have := congr_arg ( · ^^^ c ) h; simp +decide [ Nat.xor_comm ( c ^^^ _ ) c ] at this;
  linarith [Nat.sub_add_cancel (by linarith : 1 ≤ d)]

/-
A code with minimum distance d corrects all error patterns of
weight ≤ ⌊(d-1)/2⌋. The Hamming spheres of radius t = ⌊(d-1)/2⌋
around each codeword are disjoint, so nearest-codeword decoding
uniquely recovers the original.
-/
theorem correction_capacity
    (codewords : Finset ℕ)
    (d : ℕ) (hd : 3 ≤ d)
    (h_min_dist : ∀ c₁ ∈ codewords, ∀ c₂ ∈ codewords,
      c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (c : ℕ) (hc : c ∈ codewords)
    (e : ℕ) (he : hammingWeight e ≤ (d - 1) / 2) :
    ∀ c' ∈ codewords, c' ≠ c →
      hammingDist (c ^^^ e) c < hammingDist (c ^^^ e) c' := by
  -- First, `hammingDist (c ^^^ e) c = hammingWeight e` since `(c ^^^ e) ^^^ c = e`, so `hammingDist (c ^^^ e) c ≤ (d-1)/2`.
  have h_e_c : ∀ c' ∈ codewords, c' ≠ c → hammingDist (c ^^^ e) c' ≥ d - hammingWeight e := by
    intros c' hc' hc'_ne_c
    have h_triangle : hammingDist c c' ≤ hammingDist c (c ^^^ e) + hammingDist (c ^^^ e) c' := by
      exact?
    generalize_proofs at *; (
    have h_e_c : hammingDist c (c ^^^ e) = hammingWeight e := by
      unfold hammingDist hammingWeight; simp +decide [ Nat.xor_comm ] ;
    generalize_proofs at *; (
    grind))
  generalize_proofs at *; (
  have h_e_c : hammingDist (c ^^^ e) c = hammingWeight e := by
    unfold hammingDist hammingWeight; simp +decide [ Nat.xor_comm ] ;
  generalize_proofs at *; (
  grind))

/-
Singleton bound: a code of length n with minimum distance d
has at most 2^(n-d+1) codewords.
-/
theorem singleton_bound (n d : ℕ) (hd : d ≤ n + 1)
    (codewords : Finset ℕ)
    (h_len : ∀ c ∈ codewords, c < 2 ^ n)
    (h_min_dist : ∀ c₁ ∈ codewords, ∀ c₂ ∈ codewords,
      c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    codewords.card ≤ 2 ^ (n - d + 1) := by
  -- Consider the map f : codewords → ℕ defined by f(c) = c % 2^(n-d+1). This map is injective on codewords.
  have h_injective : ∀ c₁ ∈ codewords, ∀ c₂ ∈ codewords, c₁ ≠ c₂ → (c₁ % 2^(n-d+1)) ≠ (c₂ % 2^(n-d+1)) := by
    intro c₁ hc₁ c₂ hc₂ hne hmod
    have h_diff : hammingWeight (c₁ ^^^ c₂) ≤ n - (n - d + 1) := by
      -- Since $c₁ \equiv c₂ \pmod{2^{n-d+1}}$, we have $c₁ ^^^ c₂$ is divisible by $2^{n-d+1}$.
      have h_div : 2^(n-d+1) ∣ (c₁ ^^^ c₂) := by
        have h_div : (c₁ ^^^ c₂) % 2^(n-d+1) = 0 := by
          have h_xor : (c₁ ^^^ c₂) % 2^(n-d+1) = (c₁ % 2^(n-d+1)) ^^^ (c₂ % 2^(n-d+1)) := by
            exact?;
          aesop;
        exact Nat.dvd_of_mod_eq_zero h_div;
      -- Since $c₁ ^^^ c₂$ is divisible by $2^{n-d+1}$, its binary representation has at least $n-d+1$ zeros at the end.
      have h_zeros : (Nat.bits (c₁ ^^^ c₂)).take (n - d + 1) = List.replicate (n - d + 1) false := by
        obtain ⟨ k, hk ⟩ := h_div;
        rw [ hk ];
        induction n - d + 1 <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
        cases k <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
        rfl;
      -- Since $c₁ ^^^ c₂$ is less than $2^n$, its binary representation has at most $n$ bits.
      have h_bits_length : (Nat.bits (c₁ ^^^ c₂)).length ≤ n := by
        have h_bits_length : (c₁ ^^^ c₂) < 2^n := by
          exact?;
        have := @Nat.digits_len 2 ( c₁ ^^^ c₂ );
        by_cases h : c₁ ^^^ c₂ = 0 <;> simp_all +decide;
        grind +suggestions;
      have h_bits_count : (Nat.bits (c₁ ^^^ c₂)).count true ≤ (Nat.bits (c₁ ^^^ c₂)).length - (n - d + 1) := by
        rw [ ← List.take_append_drop ( n - d + 1 ) ( Nat.bits ( c₁ ^^^ c₂ ) ), List.count_append ];
        simp_all +decide [ List.count_replicate ];
        grind +splitImp;
      exact h_bits_count.trans ( Nat.sub_le_sub_right h_bits_length _ );
    unfold hammingDist at *;
    cases d <;> simp_all +decide [ Nat.sub_sub ];
    · exact hne ( Nat.mod_eq_of_lt ( show c₁ < 2 ^ ( n + 1 ) from lt_of_lt_of_le ( h_len c₁ hc₁ ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_succ _ ) ) ) ▸ Nat.mod_eq_of_lt ( show c₂ < 2 ^ ( n + 1 ) from lt_of_lt_of_le ( h_len c₂ hc₂ ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_succ _ ) ) ) ▸ hmod );
    · grind;
  have := Finset.card_le_card ( show codewords.image ( fun c => c % 2 ^ ( n - d + 1 ) ) ⊆ Finset.range ( 2 ^ ( n - d + 1 ) ) from Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Nat.mod_lt _ ( by norm_num ) ) ; simp_all +decide [ Finset.card_image_of_injOn fun c hc c' hc' => not_imp_not.mp ( h_injective c hc c' hc' ) ] ;

end Pythia.Hardware