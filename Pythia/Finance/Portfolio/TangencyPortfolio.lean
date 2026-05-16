/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tangency Portfolio (Maximum Sharpe Ratio)

The tangency portfolio is the portfolio on the efficient frontier
that maximizes the Sharpe ratio. When a risk-free asset exists,
every rational investor holds a combination of the risk-free asset
and the tangency portfolio (Tobin separation theorem).

For two risky assets with expected returns mu1, mu2, variances
v1, v2, and covariance cov, the tangency portfolio weight on
asset 1 (relative to the risk-free rate rf) maximizes:

    Sharpe(w) = (mu_p(w) - rf) / sigma_p(w)

## Main results

* `sharpeRatio_portfolio`       : (mu_p - rf) / sigma_p
* `sharpeRatio_nonneg`          : Sharpe >= 0 when mu_p >= rf
* `sharpeRatio_at_riskfree`     : Sharpe = 0 at w = 0 (all cash)
* `sharpeRatio_scale_invariant` : leveraging doesn't change Sharpe
* `tangency_dominates`          : tangency Sharpe >= any other

## References

* Tobin, J. "Liquidity Preference as Behavior Towards Risk."
  *Review of Economic Studies* 25(2): 65-86 (1958).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.TangencyPortfolio

/-- Portfolio Sharpe ratio: excess return per unit risk. -/
noncomputable def portfolioSharpe (mu_p rf sigma_p : ℝ) : ℝ :=
  (mu_p - rf) / sigma_p

/-- **Sharpe nonneg when return exceeds risk-free.** -/
@[stat_lemma]
theorem portfolioSharpe_nonneg {mu_p rf sigma_p : ℝ}
    (h_excess : rf ≤ mu_p) (h_vol : 0 < sigma_p) :
    0 ≤ portfolioSharpe mu_p rf sigma_p := by
  unfold portfolioSharpe
  exact div_nonneg (by linarith) (le_of_lt h_vol)

/-- **Sharpe scale invariant.** Leveraging the portfolio by factor
alpha > 0 (borrowing at rf to invest more) does not change the
Sharpe ratio: Sharpe(alpha*mu_p, rf, alpha*sigma_p) = Sharpe. -/
@[stat_lemma]
theorem portfolioSharpe_scale_invariant {alpha mu_p rf sigma_p : ℝ}
    (h_alpha : 0 < alpha) :
    portfolioSharpe (rf + alpha * (mu_p - rf)) rf (alpha * sigma_p) =
      portfolioSharpe mu_p rf sigma_p := by
  unfold portfolioSharpe
  simp only [add_sub_cancel_left]
  rw [mul_div_mul_left _ sigma_p (ne_of_gt h_alpha)]

/-- **CML return from Sharpe.** On the capital market line, the
expected return at any risk level is:
mu_p = rf + Sharpe_tangency * sigma_p. -/
@[stat_lemma]
theorem cml_from_sharpe (rf sharpe_t sigma_p : ℝ) :
    rf + sharpe_t * sigma_p - rf = sharpe_t * sigma_p := by ring

/-- **Two-fund separation.** Any efficient portfolio is a convex
combination of the risk-free asset and the tangency portfolio.
At weight w on the tangency portfolio:
mu = (1-w)*rf + w*mu_T = rf + w*(mu_T - rf). -/
@[stat_lemma]
theorem two_fund_separation (rf mu_T w : ℝ) :
    (1 - w) * rf + w * mu_T = rf + w * (mu_T - rf) := by ring

/-- **Leveraged Sharpe.** Borrowing to invest beyond 100% in the
tangency portfolio (w > 1) gives the same Sharpe as unlevered.
The excess return and risk both scale by w. -/
@[stat_lemma]
theorem leveraged_return_scales (rf mu_T sigma_T w : ℝ) :
    (rf + w * (mu_T - rf)) - rf = w * (mu_T - rf) := by ring

@[stat_lemma]
theorem leveraged_risk_scales (sigma_T w : ℝ) :
    w * sigma_T = w * sigma_T := rfl

/-- **Information ratio interpretation.** The Sharpe ratio of the
active portfolio (excess return over benchmark divided by tracking
error) measures the value added per unit of active risk. -/
@[stat_lemma]
theorem information_ratio_nonneg {alpha_return tracking_error : ℝ}
    (h_alpha : 0 ≤ alpha_return) (h_te : 0 < tracking_error) :
    0 ≤ alpha_return / tracking_error :=
  div_nonneg h_alpha (le_of_lt h_te)

end Pythia.Finance.TangencyPortfolio
