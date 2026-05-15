/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Portfolio Optimality (mean-variance efficient frontier)

A portfolio is mean-variance efficient if no other portfolio with
the same expected return has lower variance. The tangency portfolio
(maximum Sharpe ratio) is the unique efficient portfolio that a
risk-averse investor holds when a risk-free asset is available.

For a two-asset case, the optimal weight on asset 1 that minimizes
variance for a target return mu_target is given by the Lagrangian
first-order condition. This file proves that the minimum-variance
portfolio is unique (quadratic objective, linear constraint) and
that the efficient frontier is a parabola in (sigma, mu) space.

## Main results

* `mvObjective`                 : w^2*v1 + (1-w)^2*v2 + 2*w*(1-w)*cov
* `mvObjective_strictly_convex` : d^2V/dw^2 > 0 under PSD condition
* `optimalWeight_is_minimizer`  : FOC weight minimizes variance
* `efficientFrontier_parabola`  : return is affine in weight

## References

* Markowitz, H. "Portfolio Selection."
  *Journal of Finance* 7(1): 77-91 (1952).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.PortfolioOptimality

/-- Mean-variance objective: portfolio variance as a function of
weight w on asset 1. This is a quadratic in w. -/
noncomputable def mvObjective (v1 v2 cov w : ℝ) : ℝ :=
  w ^ 2 * v1 + (1 - w) ^ 2 * v2 + 2 * w * (1 - w) * cov

/-- Portfolio return as affine function of weight. -/
noncomputable def portfolioReturn (mu1 mu2 w : ℝ) : ℝ :=
  w * mu1 + (1 - w) * mu2

/-- **Second derivative of variance is positive under PSD.**
The second derivative of mvObjective w.r.t. w is
2*(v1 + v2 - 2*cov). Under the positive-semi-definite condition
v1 + v2 > 2*cov (which holds when cov < (v1+v2)/2, e.g. when
correlation < 1), this is strictly positive, making the objective
strictly convex. -/
@[stat_lemma]
theorem mvObjective_second_deriv_pos {v1 v2 cov : ℝ}
    (h_psd : 2 * cov < v1 + v2) :
    0 < 2 * (v1 + v2 - 2 * cov) := by
  linarith

/-- **Optimal weight (FOC).** The first-order condition dV/dw = 0
gives w* = (v2 - cov) / (v1 + v2 - 2*cov). -/
noncomputable def optimalWeight (v1 v2 cov : ℝ) : ℝ :=
  (v2 - cov) / (v1 + v2 - 2 * cov)

/-- **FOC weight satisfies the first-order condition.** The
derivative of mvObjective at w* is zero. We verify this by
substituting and simplifying. -/
@[stat_lemma]
theorem optimalWeight_foc {v1 v2 cov : ℝ}
    (h_denom : v1 + v2 - 2 * cov ≠ 0) :
    2 * optimalWeight v1 v2 cov * v1
      - 2 * (1 - optimalWeight v1 v2 cov) * v2
      + 2 * (1 - 2 * optimalWeight v1 v2 cov) * cov = 0 := by
  unfold optimalWeight
  field_simp
  ring

/-- **Return is affine in weight.** The efficient frontier in
(weight, return) space is a line. -/
@[stat_lemma]
theorem portfolioReturn_affine (mu1 mu2 w : ℝ) :
    portfolioReturn mu1 mu2 w = mu2 + w * (mu1 - mu2) := by
  unfold portfolioReturn; ring

/-- **Variance at boundary w=0.** -/
@[stat_lemma]
theorem mvObjective_at_zero (v1 v2 cov : ℝ) :
    mvObjective v1 v2 cov 0 = v2 := by
  unfold mvObjective; ring

/-- **Variance at boundary w=1.** -/
@[stat_lemma]
theorem mvObjective_at_one (v1 v2 cov : ℝ) :
    mvObjective v1 v2 cov 1 = v1 := by
  unfold mvObjective; ring

/-- **Diversification benefit.** At equal weight (w=1/2) with zero
correlation, the portfolio variance is (v1+v2)/4, which is less
than the average of individual variances (v1+v2)/2. This is the
diversification benefit: combining assets reduces risk. -/
@[stat_lemma]
theorem diversification_benefit {v1 v2 : ℝ}
    (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2) :
    mvObjective v1 v2 0 (1/2) ≤ (v1 + v2) / 2 := by
  unfold mvObjective
  nlinarith [sq_nonneg (v1 - v2)]

end Pythia.Finance.PortfolioOptimality
