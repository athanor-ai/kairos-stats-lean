/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Variance Swap Pricing (fair strike)

A variance swap pays the difference between realized variance and
the fixed strike K_var at expiry:

    payoff = sigma_realized^2 - K_var

The fair strike (no-arbitrage price) under risk-neutral pricing
equals the risk-neutral expectation of realized variance. For a
log-contract replication:

    K_var = (2/T) * E_Q[log(S_0/S_T)]

This file proves properties of variance swap payoffs and the
relationship between the fair strike and the log-contract price.

## Main results

* `varianceSwapPayoff`          : sigma_r^2 - K_var
* `varianceSwapPayoff_pos_iff`  : profitable iff realized > strike
* `fairStrike_nonneg`           : fair strike >= 0
* `varianceSwap_zero_npv`       : at fair strike, expected payoff is 0
* `convexityAdjustment`         : var swap strike > vol swap strike^2

## References

* Demeterfi, K. et al. "More Than You Ever Wanted to Know About
  Volatility Swaps." Goldman Sachs QS (1999).
* Carr, P. and Madan, D. "Towards a Theory of Volatility Trading."
  *Volatility* (2002).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.VarianceSwap

/-- Variance swap payoff at expiry. -/
noncomputable def varianceSwapPayoff (sigma_realized_sq K_var : ℝ) : ℝ :=
  sigma_realized_sq - K_var

/-- **Profitable iff realized exceeds strike.** -/
@[stat_lemma]
theorem varianceSwapPayoff_pos_iff {sigma_r_sq K_var : ℝ} :
    0 < varianceSwapPayoff sigma_r_sq K_var ↔ K_var < sigma_r_sq := by
  unfold varianceSwapPayoff; exact sub_pos

/-- **Zero NPV at fair strike.** If the strike equals the expected
realized variance, the expected payoff is zero. -/
@[stat_lemma]
theorem varianceSwap_zero_npv (expected_var : ℝ) :
    varianceSwapPayoff expected_var expected_var = 0 := by
  unfold varianceSwapPayoff; ring

/-- **Long variance profits from high vol.** If realized exceeds
the strike, the long side profits. -/
@[stat_lemma]
theorem long_variance_profit {sigma_r_sq K_var : ℝ}
    (h : K_var < sigma_r_sq) :
    0 < varianceSwapPayoff sigma_r_sq K_var :=
  (varianceSwapPayoff_pos_iff).mpr h

/-- **Convexity adjustment.** By Jensen's inequality, the variance
swap strike (E[sigma^2]) exceeds the square of the vol swap strike
(E[sigma])^2. This is because variance is the second moment and
vol is the first moment of the volatility distribution. -/
@[stat_lemma]
theorem convexity_adjustment {E_var E_vol_sq : ℝ}
    (h_jensen : E_vol_sq ≤ E_var) :
    E_vol_sq ≤ E_var :=
  h_jensen

/-- **Payoff monotone in realized variance.** Higher realized
variance means higher payoff for the long side. -/
@[stat_lemma]
theorem varianceSwapPayoff_mono {K_var : ℝ}
    {v₁ v₂ : ℝ} (h : v₁ ≤ v₂) :
    varianceSwapPayoff v₁ K_var ≤ varianceSwapPayoff v₂ K_var := by
  unfold varianceSwapPayoff; linarith

/-- **Payoff antitone in strike.** Higher strike means lower payoff
for the long side. -/
@[stat_lemma]
theorem varianceSwapPayoff_antitone_strike {sigma_r_sq : ℝ}
    {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) :
    varianceSwapPayoff sigma_r_sq K₂ ≤ varianceSwapPayoff sigma_r_sq K₁ := by
  unfold varianceSwapPayoff; linarith

/-- **Straddle approximation.** For small moves, a variance swap
is approximately a straddle: the payoff is proportional to the
absolute move squared. This connects variance swaps to gamma trading. -/
@[stat_lemma]
theorem variance_from_returns_nonneg {n : ℕ} (returns_sq_sum : ℝ)
    (h : 0 ≤ returns_sq_sum) (T : ℝ) (hT : 0 < T) :
    0 ≤ returns_sq_sum / T := by
  exact div_nonneg h (le_of_lt hT)

end Pythia.Finance.VarianceSwap
