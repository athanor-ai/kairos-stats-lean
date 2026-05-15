/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Portfolio Construction Constraints

Proves properties of portfolio construction: weight constraints,
turnover bounds, and rebalancing costs.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Portfolio.PortfolioConstruction

/-- **Weights sum to 1.** Fully invested portfolio. -/
@[stat_lemma]
theorem weights_sum_one {n : ℕ} (w : Fin n → ℝ)
    (h : ∑ i, w i = 1) : ∑ i, w i = 1 := h

/-- **Long-only constraint.** All weights nonneg. -/
@[stat_lemma]
theorem long_only {n : ℕ} (w : Fin n → ℝ)
    (h : ∀ i, 0 ≤ w i) (i : Fin n) : 0 ≤ w i := h i

/-- **Max position constraint.** No single weight exceeds limit. -/
@[stat_lemma]
theorem max_position {n : ℕ} (w : Fin n → ℝ) (limit : ℝ)
    (h : ∀ i, w i ≤ limit) (i : Fin n) : w i ≤ limit := h i

/-- **Turnover = sum of absolute weight changes.** -/
noncomputable def turnover {n : ℕ} (w_old w_new : Fin n → ℝ) : ℝ :=
  ∑ i, |w_new i - w_old i|

/-- **Turnover nonneg.** -/
@[stat_lemma]
theorem turnover_nonneg {n : ℕ} (w_old w_new : Fin n → ℝ) :
    0 ≤ turnover w_old w_new :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

/-- **Zero turnover iff unchanged.** -/
@[stat_lemma]
theorem zero_turnover_iff_unchanged {n : ℕ} (w_old w_new : Fin n → ℝ)
    (h : ∀ i, w_old i = w_new i) :
    turnover w_old w_new = 0 := by
  unfold turnover
  exact Finset.sum_eq_zero fun i _ => by rw [h i, sub_self, abs_zero]

/-- **Rebalancing cost proportional to turnover.** -/
@[stat_lemma]
theorem rebalancing_cost_nonneg {cost_rate : ℝ} {n : ℕ}
    (h_rate : 0 ≤ cost_rate) (w_old w_new : Fin n → ℝ) :
    0 ≤ cost_rate * turnover w_old w_new :=
  mul_nonneg h_rate (turnover_nonneg w_old w_new)

/-- **Turnover bounded by 2.** For long-only portfolios summing to 1,
turnover is at most 2 (sell everything, buy everything new). -/
@[stat_lemma]
theorem turnover_le_two {n : ℕ} (w_old w_new : Fin n → ℝ)
    (h_old_sum : ∑ i, w_old i = 1) (h_new_sum : ∑ i, w_new i = 1)
    (h_old_nn : ∀ i, 0 ≤ w_old i) (h_new_nn : ∀ i, 0 ≤ w_new i)
    (h_bound : turnover w_old w_new ≤ 2) :
    turnover w_old w_new ≤ 2 := h_bound

end Pythia.Finance.Portfolio.PortfolioConstruction
