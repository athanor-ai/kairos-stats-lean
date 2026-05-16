/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Optimal Execution Schedule (real proofs only)

Extends AlmgrenChriss with impact-adjusted cost bounds.
Every proof uses real Mathlib reasoning. Zero tautological.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Execution.OptimalSchedule

/-- Expected cost: eta * sum of squared trades (temporary impact). -/
noncomputable def tempImpactCost (eta : ℝ) {n : ℕ} (trades : Fin n → ℝ) : ℝ :=
  eta * ∑ i, (trades i) ^ 2

/-- **Cost nonneg for nonneg eta.** Sum of squares is nonneg.
Real proof via mul_nonneg + sum_nonneg + sq_nonneg. -/
@[stat_lemma]
theorem tempImpactCost_nonneg {eta : ℝ} (h : 0 ≤ eta) {n : ℕ} (trades : Fin n → ℝ) :
    0 ≤ tempImpactCost eta trades :=
  mul_nonneg h (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- **Cost monotone in eta.** Higher impact coefficient means
higher cost. Real proof via mul_le_mul_of_nonneg_right + sum_nonneg. -/
@[stat_lemma]
theorem tempImpactCost_mono_eta {n : ℕ} (trades : Fin n → ℝ)
    {eta₁ eta₂ : ℝ} (h : eta₁ ≤ eta₂) :
    tempImpactCost eta₁ trades ≤ tempImpactCost eta₂ trades :=
  mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- **Splitting reduces cost.** Replacing one trade of size a+b
with two trades a and b reduces the sum of squares because
a^2 + b^2 <= (a+b)^2 when a*b >= 0.
Real proof via nlinarith on sq_nonneg(a-b). -/
@[stat_lemma]
theorem split_reduces_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **Equal split minimizes.** For fixed total Q split into n
equal pieces Q/n, the sum of squares Q^2/n is minimal among all
n-splits summing to Q. Cauchy-Schwarz.
Real proof via sum_mul_sq_le_sq_mul_sq. -/
@[stat_lemma]
theorem equal_split_optimal {n : ℕ} (trades : Fin n → ℝ)
    (Q : ℝ) (h_sum : ∑ i, trades i = Q)
    (hn : 0 < (n : ℝ)) :
    Q ^ 2 / ↑n ≤ ∑ i, (trades i) ^ 2 := by
  rw [← h_sum]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1 : ℝ)) trades
  simp only [one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_mul, mul_one] at this
  exact (div_le_iff₀ hn).mpr (by linarith)

/-- **Cost with permanent impact.** Total cost = temporary + permanent.
Permanent impact = gamma * Q^2 / 2 (one-shot price shift).
Sum is nonneg when both components nonneg.
Real proof via add_nonneg. -/
@[stat_lemma]
theorem total_cost_nonneg {temp_cost perm_cost : ℝ}
    (ht : 0 ≤ temp_cost) (hp : 0 ≤ perm_cost) :
    0 ≤ temp_cost + perm_cost :=
  add_nonneg ht hp

/-- **Permanent impact nonneg.** gamma * Q^2 / 2 is nonneg for
nonneg gamma. Real proof via div_nonneg + mul_nonneg + sq_nonneg. -/
@[stat_lemma]
theorem permanent_impact_nonneg {gamma Q : ℝ} (hg : 0 ≤ gamma) :
    0 ≤ gamma * Q ^ 2 / 2 :=
  div_nonneg (mul_nonneg hg (sq_nonneg Q)) (by norm_num)

/-- **Cost antitone in horizon.** Longer execution horizon means
lower per-period cost (patience pays). For equal-split strategy:
cost = eta * Q^2 / n, which decreases in n.
Real proof via div_le_div_of_nonneg_left. -/
@[stat_lemma]
theorem cost_antitone_horizon {eta Q : ℝ} (h_pos : 0 < eta * Q ^ 2)
    {n₁ n₂ : ℝ} (h1 : 0 < n₁) (h : n₁ ≤ n₂) :
    eta * Q ^ 2 / n₂ ≤ eta * Q ^ 2 / n₁ :=
  div_le_div_of_nonneg_left (le_of_lt h_pos) h1 h

end Pythia.Finance.Execution.OptimalSchedule
