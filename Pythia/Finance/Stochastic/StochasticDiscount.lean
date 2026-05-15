/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stochastic Discount Factor (Pricing Kernel)

The **stochastic discount factor** (SDF), also called the pricing kernel,
formalizes the fundamental theorem of asset pricing.  For any asset with
payoff `x`, its price `p` satisfies

    p = E[m * x]

where `m` is the SDF.  Decomposing this expectation into mean and covariance
terms gives the algebraic form used here:

    sdfPrice(m_mean, m_payoff_cov, payoff_mean) = m_mean * payoff_mean + m_payoff_cov.

## Hansen-Jagannathan bound

The Hansen-Jagannathan bound gives a lower bound on the coefficient of
variation of the SDF in terms of observable return moments:

    sigma(m) / E[m] >= |E[r] - rf| / sigma(r).

The right-hand side, `|excess_return| / return_vol`, is formalized here as
`hansenJagannathanBound`.

## Main definitions

* `sdfPrice`                : `m_mean * payoff_mean + m_payoff_cov`
* `hansenJagannathanBound`  : `|excess_return| / return_vol`

## Main results

* `sdfPrice_at_zero_cov`              : zero covariance reduces price to mean product
* `sdfPrice_decompose`                : unfold definition as mean product plus covariance
* `hansenJagannathanBound_nonneg`     : bound is non-negative when vol is positive
* `hansenJagannathanBound_zero_excess`: bound is zero when excess return is zero
* `hansenJagannathanBound_mono_excess`: bound is monotone in |excess_return|

## References

* Hansen, L. P. and Jagannathan, R. "Implications of Security Market Data for
  Models of Dynamic Economies." *Journal of Political Economy* 99(2): 225-262
  (1991).
* Cochrane, J. H. *Asset Pricing* (revised edition). Princeton University
  Press (2005).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- SDF price: the price of an asset equals the SDF mean times the payoff
mean plus the covariance of the SDF with the payoff.

In the FTAP decomposition `E[m * x] = E[m] * E[x] + Cov(m, x)`, the scalar
parameters `m_mean`, `m_payoff_cov`, and `payoff_mean` capture the three
relevant moments without invoking measure-theoretic expectation. -/
noncomputable def sdfPrice (m_mean m_payoff_cov payoff_mean : ℝ) : ℝ :=
  m_mean * payoff_mean + m_payoff_cov

/-- Hansen-Jagannathan bound: the minimum admissible coefficient of variation
for any SDF consistent with observed excess returns and return volatility.

    hansenJagannathanBound er rv = |er| / rv

The bound holds even when the SDF is not directly observable; it constrains
the pricing kernel using only moments of observable returns. -/
noncomputable def hansenJagannathanBound (excess_return return_vol : ℝ) : ℝ :=
  |excess_return| / return_vol

/-- **Zero-covariance pricing.** When the SDF and the payoff are
uncorrelated (covariance = 0), the price equals the SDF mean times the
payoff mean. This is the risk-neutral pricing special case. -/
@[stat_lemma]
theorem sdfPrice_at_zero_cov (m_mean payoff_mean : ℝ) :
    sdfPrice m_mean 0 payoff_mean = m_mean * payoff_mean := by
  unfold sdfPrice; ring

/-- **SDF price decomposition.** The price decomposes into a mean-times-mean
term and an explicit covariance term. This is the defining identity of the
scalar SDF pricing formula. -/
@[stat_lemma]
theorem sdfPrice_decompose (m_mean cov payoff_mean : ℝ) :
    sdfPrice m_mean cov payoff_mean = m_mean * payoff_mean + cov := by
  unfold sdfPrice; ring

/-- **Non-negativity of the Hansen-Jagannathan bound.** For strictly positive
return volatility, the bound is non-negative. The proof uses `div_nonneg`
with `abs_nonneg` for the numerator and `hv.le` for the denominator. -/
@[stat_lemma]
theorem hansenJagannathanBound_nonneg (excess_return : ℝ) {return_vol : ℝ}
    (hv : 0 < return_vol) :
    0 ≤ hansenJagannathanBound excess_return return_vol := by
  unfold hansenJagannathanBound
  exact div_nonneg (abs_nonneg _) hv.le

/-- **Zero bound at zero excess return.** When the excess return is zero,
the Hansen-Jagannathan bound equals zero: a model with no excess return
imposes no lower bound on SDF volatility. -/
@[stat_lemma]
theorem hansenJagannathanBound_zero_excess (return_vol : ℝ) :
    hansenJagannathanBound 0 return_vol = 0 := by
  unfold hansenJagannathanBound
  simp [abs_zero]

/-- **Monotonicity in excess return.** For fixed strictly positive volatility,
the Hansen-Jagannathan bound is monotone in `|excess_return|`: a larger
absolute excess return demands a higher SDF volatility.

The hypotheses `h₁ : er₁ ≤ er₂` and `h₂ : -er₁ ≤ er₂` together express
`|er₁| ≤ |er₂|` via `abs_le_abs`. Dividing through by the fixed positive
`return_vol` then uses `div_le_div_of_nonneg_right`. -/
@[stat_lemma]
theorem hansenJagannathanBound_mono_excess {er₁ er₂ return_vol : ℝ}
    (hv : 0 < return_vol)
    (h₁ : er₁ ≤ er₂) (h₂ : -er₁ ≤ er₂) :
    hansenJagannathanBound er₁ return_vol ≤ hansenJagannathanBound er₂ return_vol := by
  unfold hansenJagannathanBound
  exact div_le_div_of_nonneg_right (abs_le_abs h₁ h₂) hv.le

end Pythia.Finance
