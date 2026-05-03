/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.KraftInequality

**Kraft's inequality** for binary prefix-free codes:
any prefix-free binary code satisfies `∑_a 2^{-ℓ(a)} ≤ 1`.

## Main results

* `PrefixFreeCode` — structure: an injective map `encode : α → List Bool`
  with the prefix-free property.
* `PrefixFreeCode.kraftSum` — the Kraft sum `∑_a (1/2)^{ℓ(a)}`.
* `kraft_inequality` — the main bound `kraftSum C ≤ 1`.

## Proof strategy

Binary-tree / counting argument (Cover–Thomas, Theorem 5.2.1):
pick `L ≥ max ℓ(a)`. Each codeword of length `ℓ` has `2^{L-ℓ}`
extensions to binary strings of length `L`. Prefix-freeness makes
these extension sets pairwise disjoint, so their total size
`∑_a 2^{L-ℓ(a)}` is at most `2^L`. Dividing gives the result.

## References

* Kraft, L. G. "A device for quantizing, grouping, and coding
  amplitude-modulated pulses." M.S. thesis, MIT, 1949.
* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 5.2.1.
-/

import Mathlib

open Finset BigOperators

namespace Pythia.InformationTheory

/-! ### Prefix-free code structure -/

/-- A binary prefix-free code over a finite alphabet `α`.
`encode` maps symbols to binary codewords; the prefix-free property
guarantees that no codeword is a prefix of a distinct codeword.
Injectivity follows (any list is a prefix of itself). -/
structure PrefixFreeCode (α : Type*) [Fintype α] where
  encode : α → List Bool
  prefix_free : ∀ a b : α, a ≠ b → ¬(encode a <+: encode b)

variable {α : Type*} [Fintype α]

namespace PrefixFreeCode

/-- Injectivity of a prefix-free code (since every list is a prefix of itself). -/
lemma injective (C : PrefixFreeCode α) : Function.Injective C.encode := by
  intro a b h
  by_contra hab
  exact C.prefix_free a b hab (h ▸ List.prefix_refl _)

/-- The Kraft sum of a prefix-free code: `∑_a (1/2)^{ℓ(a)}`. -/
noncomputable def kraftSum (C : PrefixFreeCode α) : ℝ :=
  ∑ a : α, ((2 : ℝ)⁻¹) ^ (C.encode a).length

end PrefixFreeCode

/-! ### Extension sets in the complete binary tree -/

/-- Binary strings of length `L` extending a word `w`:
functions `Fin L → Bool` that agree with `w` on the first `|w|` bits. -/
def codewordExtensions (w : List Bool) (L : ℕ) (hL : w.length ≤ L) :
    Finset (Fin L → Bool) :=
  Finset.univ.filter fun f =>
    ∀ (i : Fin w.length), f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ = w.get i

/-
The number of length-`L` extensions of a word `w` is `2^{L - |w|}`.
-/
lemma card_codewordExtensions (w : List Bool) (L : ℕ) (hL : w.length ≤ L) :
    (codewordExtensions w L hL).card = 2 ^ (L - w.length) := by
  set k := L - w.length
  have h_equiv : Finset.card (codewordExtensions w L hL) = Finset.card (Finset.univ : Finset (Fin k → Bool)) := by
    refine' Finset.card_bij _ _ _ _;
    use fun a ha i => a ⟨ w.length + i, by linarith [ Fin.is_lt i, Nat.sub_add_cancel hL ] ⟩;
    · grind;
    · intro a₁ ha₁ a₂ ha₂ h_eq
      ext i
      by_cases hi : i.val < w.length;
      · simp_all +decide [ funext_iff, codewordExtensions ];
        convert ha₁ ⟨ i, hi ⟩ |> Eq.trans <| ha₂ ⟨ i, hi ⟩ |> Eq.symm;
      · have := congr_fun h_eq ⟨ i - w.length, by rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i, Nat.sub_add_cancel hL ] ⟩ ; simp_all +decide [ add_tsub_cancel_of_le ( le_of_not_gt hi ) ] ;
    · intro b hb;
      refine' ⟨ fun i => if hi : i.val < w.length then w.get ⟨ i.val, hi ⟩ else b ⟨ i.val - w.length, by
        rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i, Nat.sub_add_cancel hL ] ⟩, _, _ ⟩ <;> simp_all +decide [ codewordExtensions ];
  aesop

/-
Extensions of prefix-incomparable words are disjoint.
If neither `w₁ <+: w₂` nor `w₂ <+: w₁`, no function can extend both.
-/
lemma disjoint_codewordExtensions {w₁ w₂ : List Bool} {L : ℕ}
    (hL₁ : w₁.length ≤ L) (hL₂ : w₂.length ≤ L)
    (h₁ : ¬(w₁ <+: w₂)) (h₂ : ¬(w₂ <+: w₁)) :
    Disjoint (codewordExtensions w₁ L hL₁) (codewordExtensions w₂ L hL₂) := by
  rw [ Finset.disjoint_left ] ; simp_all +decide [ codewordExtensions ];
  intro a ha; contrapose! h₁;
  refine' List.prefix_iff_eq_take.mpr _;
  refine' List.ext_get _ _ <;> simp_all +decide;
  · exact le_of_not_gt fun h => h₂ <| List.prefix_iff_eq_take.mpr <| by
      refine' List.ext_get _ _ <;> simp_all +decide;
      · linarith;
      · exact fun n hn₁ hn₂ => h₁ ⟨ n, hn₁ ⟩ ▸ ha ⟨ n, hn₂ ⟩ ▸ rfl;
  · exact fun n hn₁ hn₂ => ha ⟨ n, hn₁ ⟩ ▸ h₁ ⟨ n, hn₂ ⟩ ▸ rfl

/-! ### The natural-number Kraft bound -/

/-
**Natural-number Kraft bound**: `∑_a 2^{L - ℓ(a)} ≤ 2^L`.
Uses disjointness of extension sets in `Fin L → Bool`.
-/
lemma kraft_nat_bound (C : PrefixFreeCode α) (L : ℕ)
    (hL : ∀ a, (C.encode a).length ≤ L) :
    ∑ a : α, 2 ^ (L - (C.encode a).length) ≤ 2 ^ L := by
  have h_card : (Finset.biUnion (Finset.univ : Finset α) (fun a => codewordExtensions (C.encode a) L (hL a))).card ≤ 2 ^ L := by
    exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide [ Fintype.card_pi ] );
  rw [ Finset.card_biUnion ] at h_card;
  · convert h_card using 2 ; rw [ card_codewordExtensions ];
  · intro a _ b _ hab;
    apply disjoint_codewordExtensions;
    · exact C.prefix_free a b hab;
    · exact fun h => C.prefix_free _ _ hab.symm h

/-! ### Conversion to the real-valued Kraft inequality -/

/-
Auxiliary: `(2⁻¹ : ℝ) ^ n = 2 ^ (L - n) / 2 ^ L` when `n ≤ L`.
-/
lemma inv_two_pow_eq_div (n L : ℕ) (h : n ≤ L) :
    ((2 : ℝ)⁻¹) ^ n = (2 : ℝ) ^ (L - n) / (2 : ℝ) ^ L := by
  field_simp;
  rw [ one_div, inv_pow, inv_mul_eq_div, div_eq_iff ] <;> first | positivity | rw [ ← pow_add, Nat.sub_add_cancel h ] ;

/-
Convert the natural-number Kraft bound to the real-valued inequality.
-/
lemma kraft_sum_le_of_nat_bound (C : PrefixFreeCode α) (L : ℕ)
    (hL : ∀ a, (C.encode a).length ≤ L)
    (hnat : ∑ a : α, 2 ^ (L - (C.encode a).length) ≤ 2 ^ L) :
    C.kraftSum ≤ 1 := by
  -- Rewrite each term (2⁻¹)^l(a) as 2^{L-l(a)} / 2^L using `inv_two_pow_eq_div`.
  have h_rewrite : ∀ a, ((2 : ℝ)⁻¹) ^ (C.encode a).length = (2 : ℝ) ^ (L - (C.encode a).length) / (2 : ℝ) ^ L := by
    exact fun a => inv_two_pow_eq_div (C.encode a).length L (hL a)
  unfold PrefixFreeCode.kraftSum;
  rw [ Finset.sum_congr rfl fun a _ => h_rewrite a, ← Finset.sum_div _ _ _, div_le_one ( by positivity ) ] ; norm_cast

/-! ### Main theorem -/

/-- **Kraft's inequality** (Kraft 1949; Cover–Thomas, Theorem 5.2.1):
for any binary prefix-free code over a finite alphabet,
`∑_a 2^{-ℓ(a)} ≤ 1`. -/
theorem kraft_inequality (C : PrefixFreeCode α) : C.kraftSum ≤ 1 := by
  let L := Finset.sup Finset.univ (fun a => (C.encode a).length)
  have hL : ∀ a, (C.encode a).length ≤ L :=
    fun a => Finset.le_sup (f := fun a => (C.encode a).length) (Finset.mem_univ a)
  exact kraft_sum_le_of_nat_bound C L hL (kraft_nat_bound C L hL)

end Pythia.InformationTheory