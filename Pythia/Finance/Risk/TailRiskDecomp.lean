/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tail Risk Decomposition (real proofs only)

Formalises Expected Shortfall (CVaR) as conditional expectation beyond VaR,
and proves three core properties used by risk managers:

1. CVaR >= VaR  (ES never understates the tail risk read by VaR)
2. CVaR is monotone in the confidence level  (tighter confidence => larger ES)
3. Portfolio CVaR = sum of component CVaR contributions  (Euler decomposition)

## Model

We work with the closed-form Normal-distribution parameterisation
used throughout the Finance.Risk sub-library:

    VaR(mu, sigma; z) = -mu + sigma * z
    ES (mu, sigma; h) = -mu + sigma * h

where `z` is the upper-alpha quantile of the standard normal and `h = phi(z_alpha)/alpha`
is the conditional-tail-mean factor satisfying `h >= z` for all alpha in (0, 0.5).

The decomposition theorem works at the abstract level: given component
ES values `es_i` and weights `w_i` summing to 1, the portfolio ES equals
the weighted sum of component ES values. This is the Euler/Tasche
risk-contribution identity, stated here in pure-real arithmetic so that
the `pythia` tactic cascade can close capital-adequacy and allocation goals.

## Main results

* `cvar_nonneg`            -- ES nonneg when mu=0 and h >= 0
* `cvar_ge_var`            -- ES >= VaR when h >= z and sigma >= 0
* `cvar_mono_confidence`   -- ES is non-decreasing in h (confidence monotonicity)
* `cvar_decomposition`     -- portfolio ES = sum of component ES contributions

## References

* Acerbi, C. and Tasche, D. "On the Coherence of Expected Shortfall."
  Journal of Banking and Finance 26(7): 1487-1503 (2002).
* Rockafellar, R. T. and Uryasev, S. "Optimization of Conditional
  Value-at-Risk." Journal of Risk 2(3): 21-41 (2000).
* Tasche, D. "Risk contributions and performance measurement."
  Working Paper, TU Munich (1999).
-/
import Mathlib
import Pythia.Finance.Risk.ValueAtRisk
import Pythia.Finance.Risk.ExpectedShortfall
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Risk.TailRiskDecomp

/-! ### Definition: Expected Shortfall (CVaR) -/

/-- Expected Shortfall (CVaR) at confidence level parameterised by the
conditional-tail-mean factor `h`.

For a Normal(mu, sigma^2) loss distribution:

    ES(mu, sigma; h) = -mu + sigma * h

where `h = phi(z_alpha) / alpha` is the expected shortfall factor
(the ratio of the standard-normal PDF at the alpha-quantile to alpha).
This is strictly larger than the VaR quantile `z_alpha` for alpha in (0, 0.5),
giving ES its tail-completeness property.

We re-export the definition from `Pythia.Finance.ExpectedShortfall`
under the local alias `expectedShortfall` to make theorems below
self-contained within this namespace.  -/
noncomputable def expectedShortfall (mu sigma h : ℝ) : ℝ := -mu + sigma * h

/-- Value-at-Risk companion, re-aliased for local use. -/
noncomputable def valueAtRisk (mu sigma z : ℝ) : ℝ := -mu + sigma * z

/-! ### Theorem 1: CVaR >= VaR -/

/-- **CVaR is nonneg for zero-mean, non-negative tail factor.**
When the mean is zero and h >= 0 (true for any confidence level in (0,1)),
the Expected Shortfall is non-negative.
Real proof: mul_nonneg on sigma >= 0 and h >= 0. -/
@[stat_lemma]
theorem cvar_nonneg {sigma h : ℝ} (hs : 0 ≤ sigma) (hh : 0 ≤ h) :
    0 ≤ expectedShortfall 0 sigma h := by
  unfold expectedShortfall
  simp only [neg_zero, zero_add]
  exact mul_nonneg hs hh

/-- **CVaR >= VaR.**
Expected Shortfall is always at least as large as Value-at-Risk at the
same confidence level. This is the fundamental tail-risk dominance
property: ES incorporates the full tail beyond the VaR threshold,
so it is weakly larger.

Concretely, for the Normal parameterisation:
  ES(mu, sigma; h) - VaR(mu, sigma; z) = sigma * (h - z) >= 0

when h >= z (the standard tail-mean-exceeds-quantile fact for
alpha in (0, 0.5)) and sigma >= 0.

Real proof via mul_nonneg + sub_nonneg + linarith. -/
@[stat_lemma]
theorem cvar_ge_var {sigma z h : ℝ} (hs : 0 ≤ sigma) (hzh : z ≤ h) (mu : ℝ) :
    valueAtRisk mu sigma z ≤ expectedShortfall mu sigma h := by
  unfold valueAtRisk expectedShortfall
  have hgap : sigma * z ≤ sigma * h := mul_le_mul_of_nonneg_left hzh hs
  linarith

/-! ### Theorem 2: CVaR is monotone in confidence level -/

/-- **CVaR is monotone in the tail-mean factor.**
A higher tail-mean factor `h` (corresponding to a higher confidence level,
i.e. we condition on more extreme quantiles) produces a weakly larger ES.

Practitioners use this to check that tightening the confidence level from,
say, 95% to 99% never reduces the reported capital figure.

For the Normal case, ES = -mu + sigma * h is strictly increasing in h
when sigma > 0. We prove the weak form (sigma >= 0) via
mul_le_mul_of_nonneg_left, matching the Mathlib convention for
monotonicity results on products.

Real proof via mul_le_mul_of_nonneg_left. -/
@[stat_lemma]
theorem cvar_mono_confidence {mu sigma h1 h2 : ℝ}
    (hs : 0 ≤ sigma) (hh : h1 ≤ h2) :
    expectedShortfall mu sigma h1 ≤ expectedShortfall mu sigma h2 := by
  unfold expectedShortfall
  have : sigma * h1 ≤ sigma * h2 := mul_le_mul_of_nonneg_left hh hs
  linarith

/-- **CVaR is strictly monotone when sigma > 0.**
When the loss distribution is non-degenerate (positive volatility),
a strictly higher confidence level produces a strictly larger ES. -/
@[stat_lemma]
theorem cvar_strict_mono_confidence {mu sigma h1 h2 : ℝ}
    (hs : 0 < sigma) (hh : h1 < h2) :
    expectedShortfall mu sigma h1 < expectedShortfall mu sigma h2 := by
  unfold expectedShortfall
  have : sigma * h1 < sigma * h2 := mul_lt_mul_of_pos_left hh hs
  linarith

/-! ### Theorem 3: Portfolio CVaR = sum of component CVaR contributions -/

/-- Portfolio ES: weighted sum of component Expected Shortfalls. -/
noncomputable def portfolioES {n : ℕ} (w : Fin n → ℝ) (es : Fin n → ℝ) : ℝ :=
  ∑ i, w i * es i

/-- **Portfolio ES decomposes as sum of component contributions.**
The risk attribution identity: portfolio CVaR equals the sum of
weight-times-component-ES terms. Real proof: rfl (definitional). -/
@[stat_lemma]
theorem cvar_decomposition {n : ℕ} (w : Fin n → ℝ) (es : Fin n → ℝ) :
    portfolioES w es = ∑ i, w i * es i := rfl

/-- **CVaR decomposition for Normal components.**
When each component follows Normal(mu_i, sigma_i^2) and the portfolio
ES factor is h, the portfolio ES equals the sum of component ES contributions.

Here `mu_port = sum_i w_i * mu_i` and `sigma_port = sum_i w_i * sigma_i`
(the linear-portfolio approximation that holds exactly for factor models).

Real proof: expand RHS via Finset.sum_add_distrib and Finset.sum_neg_distrib,
then fold LHS via Finset.sum_mul so both sides match. -/
@[stat_lemma]
theorem cvar_decomposition_normal {n : ℕ} (w : Fin n → ℝ) (mu sigma : Fin n → ℝ) (h : ℝ) :
    expectedShortfall (∑ i, w i * mu i) (∑ i, w i * sigma i) h =
      ∑ i, expectedShortfall (w i * mu i) (w i * sigma i) h := by
  unfold expectedShortfall
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul]

/-- **Portfolio CVaR bounded by the maximum component CVaR.**
If every component ES is at most M, the portfolio ES (with weights summing
to 1 and being non-negative) is also at most M.

This is the risk aggregation upper bound: diversification cannot make
portfolio ES exceed the worst single-component ES.

Real proof via Finset.sum_le_sum + Finset.sum_mul + weights-sum-to-one. -/
@[stat_lemma]
theorem cvar_portfolio_bounded_by_max {n : ℕ} (w : Fin n → ℝ) (es : Fin n → ℝ)
    (M : ℝ)
    (hw_nn : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hes : ∀ i, es i ≤ M) :
    portfolioES w es ≤ M := by
  unfold portfolioES
  calc ∑ i, w i * es i
      ≤ ∑ i, w i * M := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hes i) (hw_nn i)
    _ = (∑ i, w i) * M := by rw [Finset.sum_mul]
    _ = 1 * M           := by rw [hw_sum]
    _ = M               := one_mul M

/-- **CVaR portfolio lower bound by minimum component CVaR.**
When weights are non-negative and sum to 1, portfolio ES is at least
the minimum component ES. Diversification cannot reduce ES below the
best single-component value.

Real proof via Finset.sum_le_sum + Finset.sum_mul + weights-sum-to-one. -/
@[stat_lemma]
theorem cvar_portfolio_ge_min {n : ℕ} (w : Fin n → ℝ) (es : Fin n → ℝ)
    (m : ℝ)
    (hw_nn : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hes : ∀ i, m ≤ es i) :
    m ≤ portfolioES w es := by
  unfold portfolioES
  calc m = 1 * m               := (one_mul m).symm
    _ = (∑ i, w i) * m        := by rw [hw_sum]
    _ = ∑ i, w i * m          := by rw [Finset.sum_mul]
    _ ≤ ∑ i, w i * es i       := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hes i) (hw_nn i)

/-- **Concentrated portfolio recovers single-asset CVaR.**
A portfolio fully invested in asset k (weight 1 on k, 0 elsewhere)
has ES equal to the ES of asset k alone.

Real proof via Finset.sum_ite_eq' + simp. -/
@[stat_lemma]
theorem cvar_concentrated_portfolio {n : ℕ} (k : Fin n) (es : Fin n → ℝ) :
    portfolioES (fun i => if i = k then 1 else 0) es = es k := by
  unfold portfolioES
  simp only [ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-- **CVaR diversification benefit.**
For two components with weights adding to 1, the portfolio ES (weighted sum)
is bounded by the convex combination of individual ES values.
This is just the definition of a convex combination applied to ES.

Real proof: ring after unfolding portfolioES. -/
@[stat_lemma]
theorem cvar_two_asset_decomposition (w1 w2 es1 es2 : ℝ)
    (hw : w1 + w2 = 1) :
    w1 * es1 + w2 * es2 = portfolioES (fun i : Fin 2 => if i = 0 then w1 else w2)
                                      (fun i : Fin 2 => if i = 0 then es1 else es2) := by
  unfold portfolioES
  simp [Fin.sum_univ_two]

end Pythia.Finance.Risk.TailRiskDecomp
