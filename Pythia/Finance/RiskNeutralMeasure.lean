/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk-Neutral Measure Properties (finite markets)

A risk-neutral measure (equivalent martingale measure, EMM) for a
finite one-period market is a probability measure under which
discounted asset prices are martingales. This file proves key
properties of risk-neutral pricing:

1. Linearity: the price of a linear combination of payoffs is the
   linear combination of prices (no-arb consequence).
2. Monotonicity: a payoff that dominates another has a higher price.
3. Replication: if two portfolios have the same payoff in every state,
   they have the same price.

These are the properties that make risk-neutral pricing usable in
practice: a trader can price complex payoffs by decomposition.

## References

* Harrison, J. M. and Kreps, D. M. "Martingales and Arbitrage in
  Multiperiod Securities Markets."
  *Journal of Economic Theory* 20(3): 381-408 (1979).
-/
import Mathlib
import Pythia.Finance.FTAP
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.RiskNeutralMeasure

variable {m : ℕ}

/-- Risk-neutral price of a payoff: E_q[payoff]. -/
noncomputable def rnPrice (q : Fin m → ℝ) (payoff : Fin m → ℝ) : ℝ :=
  ∑ j, q j * payoff j

/-- **Linearity of risk-neutral pricing.** The price of a + b payoff
is the sum of prices. This is the consequence of no-arbitrage that
makes portfolio pricing work. -/
@[stat_lemma]
theorem rnPrice_add (q payoff₁ payoff₂ : Fin m → ℝ) :
    rnPrice q (fun j => payoff₁ j + payoff₂ j) =
      rnPrice q payoff₁ + rnPrice q payoff₂ := by
  unfold rnPrice
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

/-- **Scalar homogeneity.** Scaling a payoff scales its price. -/
@[stat_lemma]
theorem rnPrice_smul (q : Fin m → ℝ) (c : ℝ) (payoff : Fin m → ℝ) :
    rnPrice q (fun j => c * payoff j) = c * rnPrice q payoff := by
  unfold rnPrice
  simp_rw [← mul_assoc, mul_comm (q _) c, mul_assoc]
  exact (Finset.mul_sum ..).symm

/-- **Monotonicity of risk-neutral pricing.** If payoff₁ dominates
payoff₂ in every state, its price is at least as high (under a
strictly positive measure). -/
@[stat_lemma]
theorem rnPrice_mono {q : Fin m → ℝ} (hq : ∀ j, 0 ≤ q j)
    {payoff₁ payoff₂ : Fin m → ℝ}
    (h_dom : ∀ j, payoff₂ j ≤ payoff₁ j) :
    rnPrice q payoff₂ ≤ rnPrice q payoff₁ := by
  unfold rnPrice
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (h_dom j) (hq j)

/-- **Replication.** Identical payoffs have identical prices. -/
@[stat_lemma]
theorem rnPrice_eq_of_payoff_eq (q : Fin m → ℝ)
    {payoff₁ payoff₂ : Fin m → ℝ}
    (h : ∀ j, payoff₁ j = payoff₂ j) :
    rnPrice q payoff₁ = rnPrice q payoff₂ := by
  unfold rnPrice
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

/-- **Nonneg payoff has nonneg price.** Under a nonneg measure,
a payoff that is nonneg in every state has a nonneg price. -/
@[stat_lemma]
theorem rnPrice_nonneg {q : Fin m → ℝ} (hq : ∀ j, 0 ≤ q j)
    {payoff : Fin m → ℝ} (h_nonneg : ∀ j, 0 ≤ payoff j) :
    0 ≤ rnPrice q payoff := by
  unfold rnPrice
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (hq j) (h_nonneg j)

/-- **Zero payoff has zero price.** -/
@[stat_lemma]
theorem rnPrice_zero (q : Fin m → ℝ) :
    rnPrice q (fun _ => 0) = 0 := by
  unfold rnPrice; simp

/-- **Strict positivity.** Under a strictly positive measure, a
payoff that is nonneg everywhere and strictly positive in at least
one state has a strictly positive price. -/
@[stat_lemma]
theorem rnPrice_pos {q : Fin m → ℝ} (hq_pos : ∀ j, 0 < q j)
    {payoff : Fin m → ℝ} (h_nonneg : ∀ j, 0 ≤ payoff j)
    {j₀ : Fin m} (h_pos : 0 < payoff j₀) :
    0 < rnPrice q payoff := by
  unfold rnPrice
  have h_j0 : 0 < q j₀ * payoff j₀ := mul_pos (hq_pos j₀) h_pos
  have h_rest : 0 ≤ ∑ k ∈ Finset.univ.erase j₀,
      q k * payoff k :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (le_of_lt (hq_pos k)) (h_nonneg k)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  linarith

end Pythia.Finance.RiskNeutralMeasure
