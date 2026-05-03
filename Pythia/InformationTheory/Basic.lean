/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.Basic

Foundational results for the information-theory module: Shannon entropy
non-negativity at the PMF level. First brick in the InformationTheory
expansion (ATH-938) under the ATH-937 130-theorem roadmap.
-/

import Mathlib

namespace Pythia.InformationTheory

/-- **Shannon entropy of a finite-alphabet PMF is non-negative.**
The Shannon entropy `H(p) := ∑ a, -p(a) · log(p(a))` is non-negative for any
probability mass function `p` over a finite alphabet whose values are in [0,1].

Reference: Cover-Thomas, *Elements of Information Theory* (2nd ed.), §2.1. -/
theorem shannonEntropy_nonneg
    {α : Type*} [Fintype α]
    (p : α → ℝ)
    (h_nonneg : ∀ a, 0 ≤ p a)
    (h_le_one : ∀ a, p a ≤ 1) :
    0 ≤ ∑ a, Real.negMulLog (p a) := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (h_nonneg a) (h_le_one a)

/-
Auxiliary: for a PMF value `x ∈ [0,1]` and `n ≥ 1`, we have the pointwise bound
`negMulLog(x) ≤ x * log(n) + 1/n - x`. This follows from `log(t) ≤ t - 1`
applied to `t = 1/(n*x)` when `x > 0`, and is trivial when `x = 0`.
-/
private lemma negMulLog_le_affine {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hn : 1 ≤ n) :
    Real.negMulLog x ≤ x * Real.log n + (1 : ℝ) / n - x := by
  by_cases hx' : x = 0;
  · simp +decide [ hx', Real.negMulLog ];
  · -- Use log(t) ≤ t - 1 applied to t = 1/(n*x) (which is positive).
    have h_log : Real.log (1 / (n * x)) ≤ 1 / (n * x) - 1 := by
      exact Real.log_le_sub_one_of_pos ( by positivity );
    simp_all +decide [ Real.negMulLog ];
    rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_inv, Real.log_inv ] at h_log ; nlinarith [ inv_pos.mpr ( by positivity : 0 < ( n : ℝ ) ), inv_pos.mpr ( by positivity : 0 < x ), mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : x ≠ 0 ) ]

/-
**Shannon entropy is at most log of the alphabet size.**
For a PMF `p` over a finite type `α` with `|α| = n`,
`H(p) = ∑ a, negMulLog(p a) ≤ log n`.

Proof outline: sum the pointwise bound `negMulLog_le_affine` and use `∑ p = 1`.
-/
theorem shannonEntropy_le_log_card
    {α : Type*} [Fintype α]
    (p : α → ℝ)
    (h_nonneg : ∀ a, 0 ≤ p a)
    (h_sum : ∑ a, p a = 1) :
    ∑ a, Real.negMulLog (p a) ≤ Real.log (Fintype.card α) := by
  rcases n : Fintype.card α with ( _ | _ | n ) <;> simp_all +decide;
  · rw [ Fintype.card_eq_zero_iff ] at n ; aesop;
  · obtain ⟨ a, ha ⟩ := Fintype.card_eq_one_iff.mp n;
    simp_all +decide [ Finset.sum_eq_single a, Real.negMulLog ];
  · convert Finset.sum_le_sum fun a _ => negMulLog_le_affine ( h_nonneg a ) ( by linarith : 1 ≤ ( Fintype.card α : ℕ ) ) using 1;
    simp +decide [ Finset.sum_add_distrib, h_sum, n ];
    rw [ ← Finset.sum_mul _ _ _, h_sum, one_mul, mul_inv_cancel₀ ( by linarith ) ] ; ring

end Pythia.InformationTheory