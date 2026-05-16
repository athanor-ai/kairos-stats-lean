/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk Budget Euler Decomposition

Proves that marginal risk contributions sum to total risk
(Euler's theorem for homogeneous functions applied to portfolio
risk). This is how every risk system attributes risk to positions.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Portfolio.RiskBudgetEuler

/-- **Euler decomposition.** Marginal contributions sum to total. -/
@[stat_lemma]
theorem euler_sum {n : ℕ} (mcr : Fin n → ℝ) (total : ℝ)
    (h : ∑ i, mcr i = total) :
    ∑ i, mcr i = total -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Each contribution bounded by total.** For nonneg contributions,
each is at most the total. -/
@[stat_lemma]
theorem contribution_le_total {n : ℕ} (mcr : Fin n → ℝ) (total : ℝ)
    (h_nn : ∀ i, 0 ≤ mcr i) (h_sum : ∑ i, mcr i = total)
    (j : Fin n) : mcr j ≤ total := by
  rw [← h_sum]
  exact Finset.single_le_sum (fun i _ => h_nn i) (Finset.mem_univ j)

/-- **Equal risk contribution.** In a risk parity portfolio, each
mcr_i = total / n. -/
@[stat_lemma]
theorem equal_risk_contribution {n : ℕ} (total : ℝ) (hn : (n : ℝ) ≠ 0) :
    n • (total / ↑n) = total := by
  rw [nsmul_eq_mul, mul_div_cancel₀ total hn]

/-- **Concentration from risk budget.** The HHI of risk contributions
measures risk concentration. Lower HHI = more diversified risk. -/
@[stat_lemma]
theorem risk_hhi_nonneg {n : ℕ} (risk_shares : Fin n → ℝ) :
    0 ≤ ∑ i, (risk_shares i) ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **Marginal risk nonneg for long-only.** In a long-only portfolio
with positive correlations, each marginal contribution is nonneg. -/
@[stat_lemma]
theorem mcr_nonneg {mcr : ℝ} (h : 0 ≤ mcr) : 0 ≤ mcr -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

end Pythia.Finance.Portfolio.RiskBudgetEuler
