/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Binary Symmetric Channel Capacity

The capacity of a binary symmetric channel (BSC) with crossover
probability δ ∈ (0, 1/2) is `log 2 − binEntropy(δ)`.

## Main definitions

* `bscChannel` — the BSC transition matrix on `Bool`.

## Main results

* `bsc_capacity` — `channelCapacity (bscChannel δ) = log 2 − binEntropy δ`.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Example 7.1.1 / Example 7.2.1.
-/
import Mathlib
import Pythia.InformationTheory.ChannelCapacity

open Finset BigOperators

namespace Pythia.InformationTheory

/-! ### BSC channel definition -/

/-- Binary symmetric channel with crossover probability `δ`. -/
noncomputable def bscChannel (δ : ℝ) : Bool → Bool → ℝ :=
  fun a b => if a = b then 1 - δ else δ

/-- Uniform distribution on `Bool`. -/
noncomputable def uniformBool : Bool → ℝ := fun _ => 1 / 2

/-! ### Key identity: mutual information for BSC equals output entropy minus H(δ)

For any valid input distribution `p` on Bool and BSC with parameter `δ ∈ (0, 1/2)`,

  `mutualInfo p (bscChannel δ) = binEntropy(q) − binEntropy(δ)`

where `q = p(false)·(1−δ) + p(true)·δ` is the output marginal for `false`.
-/

/-- Output marginal probability for `false` given input distribution `p` and BSC(δ). -/
noncomputable def bscOutputFalse (p : Bool → ℝ) (δ : ℝ) : ℝ :=
  p false * (1 - δ) + p true * δ

/-- `binEntropy p = negMulLog p + negMulLog (1 - p)` -/
lemma binEntropy_eq_negMulLog_add (p : ℝ) :
    Real.binEntropy p = Real.negMulLog p + Real.negMulLog (1 - p) := by
  unfold Real.binEntropy Real.negMulLog
  simp [Real.log_inv]
  ring

/-
The mutual information of any valid input distribution through BSC(δ)
equals `binEntropy(q) − binEntropy(δ)` where `q` is the output marginal.
-/
lemma mutualInfo_bsc_eq
    (p : Bool → ℝ) (δ : ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : p false + p true = 1)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2) :
    mutualInfo p (bscChannel δ) =
      Real.binEntropy (bscOutputFalse p δ) - Real.binEntropy δ := by
  unfold mutualInfo bscChannel bscOutputFalse Real.binEntropy;
  rw [ Finset.sum_eq_add ( Bool.true ) ( Bool.false ) ] <;> norm_num;
  rw [ Real.log_div, Real.log_div ] <;> try nlinarith;
  · rw [ Real.log_div, Real.log_div ] <;> try nlinarith;
    · grind;
    · cases lt_or_eq_of_le ( hp_nonneg true ) <;> cases lt_or_eq_of_le ( hp_nonneg false ) <;> nlinarith;
    · cases lt_or_eq_of_le ( hp_nonneg true ) <;> cases lt_or_eq_of_le ( hp_nonneg false ) <;> nlinarith;
  · cases lt_or_eq_of_le ( hp_nonneg true ) <;> cases lt_or_eq_of_le ( hp_nonneg false ) <;> nlinarith;
  · cases lt_or_eq_of_le ( hp_nonneg true ) <;> cases lt_or_eq_of_le ( hp_nonneg false ) <;> nlinarith

/-
At the uniform input distribution, the BSC output marginal is 1/2.
-/
lemma bscOutputFalse_uniform (δ : ℝ) :
    bscOutputFalse uniformBool δ = 1 / 2 := by
  unfold bscOutputFalse uniformBool; ring;

/-
Mutual information at the uniform input achieves `log 2 − binEntropy(δ)`.
-/
lemma mutualInfo_bsc_uniform (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2) :
    mutualInfo uniformBool (bscChannel δ) = Real.log 2 - Real.binEntropy δ := by
  convert mutualInfo_bsc_eq uniformBool δ _ _ hδ_pos hδ_lt using 2 <;> norm_num [ bscOutputFalse_uniform ];
  · rw [ ← Real.binEntropy_two_inv, inv_eq_one_div ];
  · exact ⟨ by unfold uniformBool; norm_num, by unfold uniformBool; norm_num ⟩;
  · unfold uniformBool; norm_num;

/-
The uniform distribution on Bool is a valid PMF.
-/
lemma uniformBool_valid : (∀ a : Bool, 0 ≤ uniformBool a) ∧
    ∑ a : Bool, uniformBool a = 1 := by
  unfold uniformBool; norm_num;

/-
Mutual information through BSC(δ) is at most `log 2 − binEntropy(δ)`.
-/
lemma mutualInfo_bsc_le (p : Bool → ℝ) (δ : ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : p false + p true = 1)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2) :
    mutualInfo p (bscChannel δ) ≤ Real.log 2 - Real.binEntropy δ := by
  rw [ mutualInfo_bsc_eq p δ hp_nonneg hp_sum hδ_pos hδ_lt ];
  apply_rules [ sub_le_sub_right, Real.binEntropy_le_log_two ]

/-
**BSC Channel Capacity.**

The capacity of the binary symmetric channel with crossover probability
`δ ∈ (0, 1/2)` is `log 2 − binEntropy(δ)`.

  C(BSC(δ)) = log 2 − H_b(δ)

The maximum is achieved by the uniform input distribution (p = 1/2),
which yields output entropy `log 2`.

Citation: Cover–Thomas Example 7.1.1 / Example 7.2.1.
-/
theorem bsc_capacity (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2) :
    channelCapacity (bscChannel δ) = Real.log 2 - Real.binEntropy δ := by
  refine' le_antisymm _ _;
  · convert ciSup_le _;
    · exact ⟨ ⟨ fun _ => 1 / 2, fun _ => by norm_num, by norm_num ⟩ ⟩;
    · intro x;
      convert mutualInfo_bsc_le x.val δ x.property.1 _ hδ_pos hδ_lt;
      convert x.2.2 using 1;
      rw [ Finset.sum_eq_add ] <;> norm_num;
  · refine' le_csSup _ _;
    · refine' ⟨ Real.log 2 - Real.binEntropy δ, Set.forall_mem_range.2 fun p => _ ⟩;
      convert mutualInfo_bsc_le p.val δ p.property.1 _ hδ_pos hδ_lt using 1;
      convert p.2.2 using 1;
      rw [ Finset.sum_eq_add ] <;> norm_num;
    · exact ⟨ ⟨ uniformBool, uniformBool_valid ⟩, mutualInfo_bsc_uniform δ hδ_pos hδ_lt ⟩

end Pythia.InformationTheory