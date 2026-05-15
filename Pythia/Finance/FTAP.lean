/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# First Fundamental Theorem of Asset Pricing (finite, one-period)

The first fundamental theorem of asset pricing (FTAP) states that a
finite one-period market admits no arbitrage if and only if there
exists an equivalent risk-neutral (martingale) probability measure.

For a finite market with `n` assets and `m` states:
- Asset payoffs are an `n x m` real matrix `D`.
- Asset prices are a vector `p : Fin n -> R`.
- A portfolio is `theta : Fin n -> R`.
- Arbitrage is a portfolio with `p . theta <= 0` and
  `D^T theta >= 0` componentwise with at least one strict inequality.

The easy direction (risk-neutral measure implies no arbitrage) is
purely algebraic: if `q` is a strictly positive probability vector
with `p = D q`, then any portfolio with nonneg payoff in all states
and nonpos cost must have zero payoff in all states.

This file proves the easy direction of the FTAP for finite markets.
The hard direction (no arbitrage implies existence of `q`) requires
the separating hyperplane theorem (Hahn-Banach); it is deferred to
a frontier module.

## Main results

* `riskNeutralImpliesNoArbitrage` : the easy direction of FTAP
* `riskNeutralPricing`           : price = expected discounted payoff

## References

* Harrison, J. M. and Kreps, D. M. "Martingales and Arbitrage in
  Multiperiod Securities Markets."
  *Journal of Economic Theory* 20(3): 381-408 (1979).
* Harrison, J. M. and Pliska, S. R. "Martingales and Stochastic
  Integrals in the Theory of Continuous Trading."
  *Stochastic Processes and their Applications* 11(3): 215-260 (1981).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.FTAP

variable {n m : ℕ}

/-- A risk-neutral probability vector: strictly positive weights summing to 1. -/
structure RiskNeutralMeasure (m : ℕ) where
  q : Fin m → ℝ
  q_pos : ∀ j, 0 < q j
  q_sum_one : ∑ j : Fin m, q j = 1

/-- Risk-neutral pricing: the price of asset `i` equals the expected
payoff under `q`: `p_i = sum_j q_j * D_ij`. -/
def isRiskNeutralPrice (D : Fin n → Fin m → ℝ) (p : Fin n → ℝ)
    (rnm : RiskNeutralMeasure m) : Prop :=
  ∀ i, p i = ∑ j, rnm.q j * D i j

/-- **Risk-neutral pricing identity.** Under a risk-neutral measure,
the price of a portfolio equals the expected payoff:
`theta . p = sum_j q_j * (sum_i theta_i * D_ij)`. -/
@[stat_lemma]
theorem portfolio_pricing
    (D : Fin n → Fin m → ℝ) (p : Fin n → ℝ)
    (rnm : RiskNeutralMeasure m)
    (h_rn : isRiskNeutralPrice D p rnm)
    (theta : Fin n → ℝ) :
    ∑ i, theta i * p i =
      ∑ j, rnm.q j * ∑ i, theta i * D i j := by
  conv_lhs => arg 2; ext i; rw [h_rn i]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i; ring

/-- **Easy direction of FTAP.** Under risk-neutral pricing, if a
portfolio has nonneg payoff in every state (`sum_i theta_i * D_ij >= 0`
for all j) and nonpositive cost (`sum_i theta_i * p_i <= 0`), then
the portfolio cost is exactly zero and the payoff is zero in every
state.

This is the no-arbitrage implication: risk-neutral measure existence
rules out free lunches. -/
@[stat_lemma]
theorem riskNeutralImpliesNoArbitrage
    (D : Fin n → Fin m → ℝ) (p : Fin n → ℝ)
    (rnm : RiskNeutralMeasure m)
    (h_rn : isRiskNeutralPrice D p rnm)
    (theta : Fin n → ℝ)
    (h_nonneg_payoff : ∀ j, 0 ≤ ∑ i, theta i * D i j)
    (h_nonpos_cost : ∑ i, theta i * p i ≤ 0) :
    (∑ i, theta i * p i = 0) ∧
    (∀ j, ∑ i, theta i * D i j = 0) := by
  have h_pricing := portfolio_pricing D p rnm h_rn theta
  have h_expected_nonneg : 0 ≤ ∑ j, rnm.q j * ∑ i, theta i * D i j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (le_of_lt (rnm.q_pos j)) (h_nonneg_payoff j)
  have h_cost_zero : ∑ i, theta i * p i = 0 := by
    linarith [h_pricing]
  constructor
  · exact h_cost_zero
  · intro j
    by_contra h_ne
    have h_pos_j : 0 < ∑ i, theta i * D i j := by
      exact lt_of_le_of_ne (h_nonneg_payoff j) (Ne.symm h_ne)
    have h_strict : 0 < rnm.q j * ∑ i, theta i * D i j :=
      mul_pos (rnm.q_pos j) h_pos_j
    have h_rest_nonneg : 0 ≤ ∑ k ∈ Finset.univ.erase j, rnm.q k * ∑ i, theta i * D i k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (le_of_lt (rnm.q_pos k)) (h_nonneg_payoff k)
    have h_sum_split : ∑ k : Fin m, rnm.q k * ∑ i, theta i * D i k =
        rnm.q j * ∑ i, theta i * D i j +
        ∑ k ∈ Finset.univ.erase j, rnm.q k * ∑ i, theta i * D i k := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    rw [← h_pricing, h_cost_zero] at h_sum_split
    linarith

end Pythia.Finance.FTAP
