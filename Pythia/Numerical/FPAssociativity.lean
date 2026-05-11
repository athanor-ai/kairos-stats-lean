/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Floating-Point Associativity Error Bounds (Higham)

Floating-point addition is NOT associative: `fl(fl(a+b)+c) ≠ fl(a+fl(b+c))` in
general. This module proves formal bounds on the associativity gap using the
standard relative-error model of floating-point arithmetic.

## Standard floating-point model

Each arithmetic operation satisfies:

  fl(a + b) = (a + b)(1 + δ)   where |δ| ≤ ε

where ε is the machine epsilon (unit roundoff). This is the standard
relative-error model (Higham, §2.2).

## Main results

* `fp_add_commutative` — FP addition is commutative under the standard model.

* `fp_add_assoc_bound` — the main associativity error bound:
    |fl(fl(a+b)+c) - fl(a+fl(b+c))| ≤ 4·ε·(1+ε)·(|a|+|b|+|c|)

* `fp_sum_order_bound` — corollary: different summation orders differ by the
  same bound.

* `pairwise_summation_bound` — pairwise (recursive) summation of a
  `Fin (2^d)` vector has error ≤ ((1+ε)^d - 1)·Σ|xᵢ|, i.e. O(log n · ε).

## References

* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). §4.1 (floating-point model), Theorem 4.1.
-/
import Mathlib

namespace Pythia.Numerical.FPAssociativity

/-! ## Floating-point addition model -/

/-- The standard floating-point addition model. `fp_add eps a b` satisfies
the relative-error bound fl(a + b) = (a + b)(1 + δ) where |δ| ≤ eps. -/
structure FPAddModel (eps : ℝ) where
  /-- The floating-point addition operation. -/
  fp_add : ℝ → ℝ → ℝ
  /-- Rounding error witness δ(a,b): fp_add a b = (a+b)*(1 + delta a b). -/
  delta : ℝ → ℝ → ℝ
  /-- Model equation: fl(a+b) = (a+b)*(1+δ). -/
  model_eq : ∀ a b, fp_add a b = (a + b) * (1 + delta a b)
  /-- Machine-epsilon bound on the rounding error. -/
  delta_bound : ∀ a b, |delta a b| ≤ eps
  /-- ε is nonneg. -/
  eps_nonneg : 0 ≤ eps

/-! ## Commutativity -/

/-- **FP addition is commutative** under the standard model, provided that
the rounding error δ is symmetric: δ(a,b) = δ(b,a). -/
theorem fp_add_commutative
    (eps : ℝ) (model : FPAddModel eps)
    (a b : ℝ)
    (h_sym : model.delta a b = model.delta b a) :
    model.fp_add a b = model.fp_add b a := by
  rw [model.model_eq a b, model.model_eq b a, add_comm b a, h_sym]

/-! ## Associativity error bound -/

/-- Algebraic associativity gap bound.

For real δ₁, δ₂, δ₃, δ₄ ∈ [-ε, ε] and pa, pb, pc ≥ 0 bounding |a|, |b|, |c|:

  |((a+b)(1+δ₁)+c)(1+δ₂) - (a+(b+c)(1+δ₃))(1+δ₄)| ≤ 4·ε·(1+ε)·(pa+pb+pc) -/
private lemma assoc_gap_le
    {eps a b c d₁ d₂ d₃ d₄ pa pb pc : ℝ}
    (hε : 0 ≤ eps)
    (h₁lo : -eps ≤ d₁) (h₁hi : d₁ ≤ eps)
    (h₂lo : -eps ≤ d₂) (h₂hi : d₂ ≤ eps)
    (h₃lo : -eps ≤ d₃) (h₃hi : d₃ ≤ eps)
    (h₄lo : -eps ≤ d₄) (h₄hi : d₄ ≤ eps)
    (hpa : 0 ≤ pa) (hpb : 0 ≤ pb) (hpc : 0 ≤ pc)
    (ha_lo : -pa ≤ a) (ha_hi : a ≤ pa)
    (hb_lo : -pb ≤ b) (hb_hi : b ≤ pb)
    (hc_lo : -pc ≤ c) (hc_hi : c ≤ pc) :
    |((a + b) * (1 + d₁) + c) * (1 + d₂) - (a + (b + c) * (1 + d₃)) * (1 + d₄)| ≤
      4 * eps * (1 + eps) * (pa + pb + pc) := by
  -- Decompose: difference = P - Q where P and Q encode left-first / right-first errors
  set P := (a + b) * d₁ * (1 + d₂) + (a + b + c) * d₂
  set Q := (b + c) * d₃ * (1 + d₄) + (a + b + c) * d₄
  have key : ((a + b) * (1 + d₁) + c) * (1 + d₂) - (a + (b + c) * (1 + d₃)) * (1 + d₄) =
      P - Q := by simp only [P, Q]; ring
  rw [key]
  have h_ab  : |a + b| ≤ pa + pb          := by rw [abs_le]; constructor <;> linarith
  have h_bc  : |b + c| ≤ pb + pc          := by rw [abs_le]; constructor <;> linarith
  have h_abc : |a + b + c| ≤ pa + pb + pc := by rw [abs_le]; constructor <;> linarith
  have hd₁   : |d₁| ≤ eps                := abs_le.mpr ⟨h₁lo, h₁hi⟩
  have hd₂   : |d₂| ≤ eps                := abs_le.mpr ⟨h₂lo, h₂hi⟩
  have hd₃   : |d₃| ≤ eps                := abs_le.mpr ⟨h₃lo, h₃hi⟩
  have hd₄   : |d₄| ≤ eps                := abs_le.mpr ⟨h₄lo, h₄hi⟩
  have h_1d₂ : |1 + d₂| ≤ 1 + eps       := by rw [abs_le]; constructor <;> linarith
  have h_1d₄ : |1 + d₄| ≤ 1 + eps       := by rw [abs_le]; constructor <;> linarith
  -- Bound |P| and |Q| independently via triangle inequality
  have hboundP : |P| ≤ (pa + pb) * eps * (1 + eps) + (pa + pb + pc) * eps := by
    simp only [P]
    calc |(a + b) * d₁ * (1 + d₂) + (a + b + c) * d₂|
        ≤ |(a + b) * d₁ * (1 + d₂)| + |(a + b + c) * d₂| := abs_add_le _ _
      _ = |a + b| * |d₁| * |1 + d₂| + |a + b + c| * |d₂| := by
            rw [abs_mul, abs_mul, abs_mul]
      _ ≤ (pa + pb) * eps * (1 + eps) + (pa + pb + pc) * eps := by gcongr
  have hboundQ : |Q| ≤ (pb + pc) * eps * (1 + eps) + (pa + pb + pc) * eps := by
    simp only [Q]
    calc |(b + c) * d₃ * (1 + d₄) + (a + b + c) * d₄|
        ≤ |(b + c) * d₃ * (1 + d₄)| + |(a + b + c) * d₄| := abs_add_le _ _
      _ = |b + c| * |d₃| * |1 + d₄| + |a + b + c| * |d₄| := by
            rw [abs_mul, abs_mul, abs_mul]
      _ ≤ (pb + pc) * eps * (1 + eps) + (pa + pb + pc) * eps := by gcongr
  -- |P - Q| ≤ |P| + |Q| by triangle inequality
  have hPQ : |P - Q| ≤ |P| + |Q| := by
    have h := abs_add_le P (-Q)
    rwa [abs_neg, ← sub_eq_add_neg] at h
  nlinarith [mul_nonneg hε hε]

/-- **Floating-point associativity error bound** (Higham §4.1).

For the standard model fl(a + b) = (a + b)(1 + δ) with |δ| ≤ ε, the
associativity gap satisfies:

  |fl(fl(a+b)+c) - fl(a+fl(b+c))| ≤ 4·ε·(1+ε)·(|a|+|b|+|c|) -/
theorem fp_add_assoc_bound
    (eps : ℝ) (model : FPAddModel eps)
    (a b c : ℝ) :
    |model.fp_add (model.fp_add a b) c - model.fp_add a (model.fp_add b c)| ≤
      4 * eps * (1 + eps) * (|a| + |b| + |c|) := by
  have lhs_eq :
      model.fp_add (model.fp_add a b) c =
        ((a + b) * (1 + model.delta a b) + c) *
          (1 + model.delta ((a + b) * (1 + model.delta a b)) c) := by
    rw [model.model_eq (model.fp_add a b) c, model.model_eq a b]
  have rhs_eq :
      model.fp_add a (model.fp_add b c) =
        (a + (b + c) * (1 + model.delta b c)) *
          (1 + model.delta a ((b + c) * (1 + model.delta b c))) := by
    rw [model.model_eq a (model.fp_add b c), model.model_eq b c]
  rw [lhs_eq, rhs_eq]
  apply assoc_gap_le model.eps_nonneg
  · exact (abs_le.mp (model.delta_bound a b)).1
  · exact (abs_le.mp (model.delta_bound a b)).2
  · exact (abs_le.mp (model.delta_bound ((a + b) * (1 + model.delta a b)) c)).1
  · exact (abs_le.mp (model.delta_bound ((a + b) * (1 + model.delta a b)) c)).2
  · exact (abs_le.mp (model.delta_bound b c)).1
  · exact (abs_le.mp (model.delta_bound b c)).2
  · exact (abs_le.mp (model.delta_bound a ((b + c) * (1 + model.delta b c)))).1
  · exact (abs_le.mp (model.delta_bound a ((b + c) * (1 + model.delta b c)))).2
  · exact abs_nonneg a
  · exact abs_nonneg b
  · exact abs_nonneg c
  · exact neg_abs_le a
  · exact le_abs_self a
  · exact neg_abs_le b
  · exact le_abs_self b
  · exact neg_abs_le c
  · exact le_abs_self c

/-! ## Different summation orders -/

/-- **Summation-order error bound** for three numbers. -/
theorem fp_sum_order_bound
    (eps : ℝ) (model : FPAddModel eps)
    (a b c : ℝ) :
    |model.fp_add (model.fp_add a b) c - model.fp_add a (model.fp_add b c)| ≤
      4 * eps * (1 + eps) * (|a| + |b| + |c|) :=
  fp_add_assoc_bound eps model a b c

/-! ## Pairwise summation -/

/-- Exact sum of a `Fin (2^d)`-indexed vector. -/
noncomputable def exactPairwiseSum {d : ℕ} (x : Fin (2 ^ d) → ℝ) : ℝ :=
  ∑ i, x i

private lemma pow_succ_lt_left (d : ℕ) (i : Fin (2 ^ d)) :
    i.val < 2 ^ (d + 1) := by have h := i.isLt; simp only [pow_succ]; omega

private lemma pow_succ_lt_right (d : ℕ) (i : Fin (2 ^ d)) :
    i.val + 2 ^ d < 2 ^ (d + 1) := by have h := i.isLt; simp only [pow_succ]; omega

/-- FP pairwise summation: recursively sum each half, then add. -/
noncomputable def fpPairwiseSum (eps : ℝ) (model : FPAddModel eps) :
    ∀ {d : ℕ}, (Fin (2 ^ d) → ℝ) → ℝ
  | 0, x => x ⟨0, by norm_num⟩
  | d + 1, x =>
    model.fp_add
      (fpPairwiseSum eps model (fun i : Fin (2 ^ d) =>
        x ⟨i.val, pow_succ_lt_left d i⟩))
      (fpPairwiseSum eps model (fun i : Fin (2 ^ d) =>
        x ⟨i.val + 2 ^ d, pow_succ_lt_right d i⟩))

/-- The exact sum splits over left and right halves. -/
private lemma exactPairwiseSum_split {d : ℕ} (x : Fin (2 ^ (d + 1)) → ℝ) :
    exactPairwiseSum x =
      exactPairwiseSum (fun i : Fin (2 ^ d) => x ⟨i.val, pow_succ_lt_left d i⟩) +
      exactPairwiseSum (fun i : Fin (2 ^ d) => x ⟨i.val + 2 ^ d, pow_succ_lt_right d i⟩) := by
  simp only [exactPairwiseSum]
  have h2 : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by ring
  have step1 : ∑ i : Fin (2 ^ (d + 1)), x i =
      ∑ i : Fin (2 ^ d + 2 ^ d), x ⟨i.val, h2 ▸ i.isLt⟩ :=
    Fintype.sum_equiv (finCongr h2.symm) _ _ (fun i => by simp [finCongr])
  rw [step1, Fin.sum_univ_add]
  congr 1
  all_goals {
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext
    simp
  }

/-- Sum of absolute values also splits. -/
private lemma sum_abs_split {d : ℕ} (x : Fin (2 ^ (d + 1)) → ℝ) :
    ∑ i : Fin (2 ^ (d + 1)), |x i| =
      ∑ i : Fin (2 ^ d), |x ⟨i.val, pow_succ_lt_left d i⟩| +
      ∑ i : Fin (2 ^ d), |x ⟨i.val + 2 ^ d, pow_succ_lt_right d i⟩| := by
  have h2 : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by ring
  have step1 : ∑ i : Fin (2 ^ (d + 1)), |x i| =
      ∑ i : Fin (2 ^ d + 2 ^ d), |x ⟨i.val, h2 ▸ i.isLt⟩| :=
    Fintype.sum_equiv (finCongr h2.symm) _ _ (fun i => by simp [finCongr])
  rw [step1, Fin.sum_univ_add]
  congr 1
  all_goals {
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    ext
    simp
  }

/-- **Pairwise summation error bound** (inductive, exact form).

  |fpPairwiseSum x - Σᵢ xᵢ| ≤ ((1+ε)^d - 1) · Σᵢ |xᵢ|  -/
theorem pairwise_summation_bound
    (eps : ℝ) (model : FPAddModel eps)
    (d : ℕ) (x : Fin (2 ^ d) → ℝ) :
    |fpPairwiseSum eps model x - exactPairwiseSum x| ≤
      ((1 + eps) ^ d - 1) * ∑ i, |x i| := by
  induction d with
  | zero =>
    simp only [fpPairwiseSum, exactPairwiseSum, pow_zero]
    rw [show ∑ i : Fin (2 ^ 0), x i = x ⟨0, by norm_num⟩ from by
      norm_num; exact Fin.sum_univ_one _]
    simp
  | succ d ih =>
    let L : Fin (2 ^ d) → ℝ := fun i => x ⟨i.val, pow_succ_lt_left d i⟩
    let R : Fin (2 ^ d) → ℝ := fun i => x ⟨i.val + 2 ^ d, pow_succ_lt_right d i⟩
    have fp_eq : fpPairwiseSum eps model x =
        model.fp_add (fpPairwiseSum eps model L) (fpPairwiseSum eps model R) := rfl
    have exact_eq : exactPairwiseSum x = exactPairwiseSum L + exactPairwiseSum R :=
      exactPairwiseSum_split x
    let s_L := fpPairwiseSum eps model L
    let s_R := fpPairwiseSum eps model R
    let e_L := exactPairwiseSum L
    let e_R := exactPairwiseSum R
    let SL  := ∑ i, |L i|
    let SR  := ∑ i, |R i|
    have ih_L : |s_L - e_L| ≤ ((1 + eps) ^ d - 1) * SL := ih L
    have ih_R : |s_R - e_R| ≤ ((1 + eps) ^ d - 1) * SR := ih R
    have hδ  : |model.delta s_L s_R| ≤ eps := model.delta_bound s_L s_R
    have hfp : model.fp_add s_L s_R = (s_L + s_R) * (1 + model.delta s_L s_R) :=
      model.model_eq s_L s_R
    have hε   : 0 ≤ eps := model.eps_nonneg
    have hSL  : 0 ≤ SL := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hSR  : 0 ≤ SR := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hpow : 0 ≤ (1 + eps) ^ d := pow_nonneg (by linarith) d
    have h_eL : |e_L| ≤ SL := Finset.abs_sum_le_sum_abs _ _
    have h_eR : |e_R| ≤ SR := Finset.abs_sum_le_sum_abs _ _
    have h_abs_sL : |s_L| ≤ (1 + eps) ^ d * SL := by
      calc |s_L| = |e_L + (s_L - e_L)| := by ring_nf
        _ ≤ |e_L| + |s_L - e_L|        := abs_add_le _ _
        _ ≤ SL + ((1 + eps) ^ d - 1) * SL := by linarith
        _ = (1 + eps) ^ d * SL             := by ring
    have h_abs_sR : |s_R| ≤ (1 + eps) ^ d * SR := by
      calc |s_R| = |e_R + (s_R - e_R)| := by ring_nf
        _ ≤ |e_R| + |s_R - e_R|        := abs_add_le _ _
        _ ≤ SR + ((1 + eps) ^ d - 1) * SR := by linarith
        _ = (1 + eps) ^ d * SR             := by ring
    have h_abs_sum : |s_L + s_R| ≤ (1 + eps) ^ d * (SL + SR) :=
      calc |s_L + s_R| ≤ |s_L| + |s_R|                               := abs_add_le _ _
        _ ≤ (1 + eps) ^ d * SL + (1 + eps) ^ d * SR := by linarith
        _ = (1 + eps) ^ d * (SL + SR)               := by ring
    have h_outer : |(s_L + s_R) * (1 + model.delta s_L s_R) - (e_L + e_R)| ≤
        ((1 + eps) ^ d - 1) * (SL + SR) + (1 + eps) ^ d * (SL + SR) * eps := by
      have decomp : (s_L + s_R) * (1 + model.delta s_L s_R) - (e_L + e_R) =
          (s_L - e_L) + (s_R - e_R) + (s_L + s_R) * model.delta s_L s_R := by ring
      have h_dt : |(s_L + s_R) * model.delta s_L s_R| ≤ (1 + eps) ^ d * (SL + SR) * eps := by
        have hmul : |(s_L + s_R) * model.delta s_L s_R| =
            |s_L + s_R| * |model.delta s_L s_R| := abs_mul _ _
        rw [hmul]
        exact mul_le_mul h_abs_sum hδ (abs_nonneg _) (by positivity)
      rw [decomp]
      calc |(s_L - e_L) + (s_R - e_R) + (s_L + s_R) * model.delta s_L s_R|
          ≤ |(s_L - e_L) + (s_R - e_R)| + |(s_L + s_R) * model.delta s_L s_R| :=
              abs_add_le _ _
        _ ≤ (|s_L - e_L| + |s_R - e_R|) + (1 + eps) ^ d * (SL + SR) * eps := by
              linarith [abs_add_le (s_L - e_L) (s_R - e_R)]
        _ ≤ ((1 + eps) ^ d - 1) * SL + ((1 + eps) ^ d - 1) * SR +
              (1 + eps) ^ d * (SL + SR) * eps := by linarith
        _ = ((1 + eps) ^ d - 1) * (SL + SR) + (1 + eps) ^ d * (SL + SR) * eps := by ring
    rw [fp_eq, hfp, exact_eq, sum_abs_split x]
    linarith [show ((1 + eps) ^ d - 1) * (SL + SR) + (1 + eps) ^ d * (SL + SR) * eps =
        ((1 + eps) ^ (d + 1) - 1) * (SL + SR) by rw [pow_succ]; ring]

/-! ## Corollary: linear-in-eps bound -/

/-- **Pairwise summation linear-in-eps bound.**

For `2·d·ε ≤ 1`, `(1+ε)^d - 1 ≤ 2·d·ε`, giving:

  |fpPairwiseSum x - Σᵢ xᵢ| ≤ 2·d·ε·Σᵢ|xᵢ|  -/
theorem pairwise_summation_linear_bound
    (eps : ℝ) (model : FPAddModel eps)
    (d : ℕ) (x : Fin (2 ^ d) → ℝ)
    (h_small : 2 * (d : ℝ) * eps ≤ 1) :
    |fpPairwiseSum eps model x - exactPairwiseSum x| ≤
      2 * (d : ℝ) * eps * ∑ i, |x i| := by
  have hε : 0 ≤ eps := model.eps_nonneg
  have hS : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have base := pairwise_summation_bound eps model d x
  suffices h_pow : (1 + eps) ^ d - 1 ≤ 2 * (d : ℝ) * eps by
    linarith [mul_le_mul_of_nonneg_right h_pow hS]
  suffices ∀ (n : ℕ), 2 * (n : ℝ) * eps ≤ 1 → (1 + eps) ^ n - 1 ≤ 2 * n * eps from
    this d h_small
  intro n hn
  induction n with
  | zero => simp
  | succ k ih_k =>
    push_cast at hn ⊢
    have hk_mul : 2 * (k : ℝ) * eps ≤ 1 := by linarith
    have heps_half : eps ≤ 1 / 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have ih' : (1 + eps) ^ k - 1 ≤ 2 * ↑k * eps := ih_k hk_mul
    rw [pow_succ]
    have hpow_k : 0 ≤ (1 + eps) ^ k := pow_nonneg (by linarith) k
    nlinarith [sq_nonneg eps]

end Pythia.Numerical.FPAssociativity
