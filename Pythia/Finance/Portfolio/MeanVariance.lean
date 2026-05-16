/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mean-Variance Optimization (Markowitz, 1952): Core Algebraic Spec

This file establishes the algebraic foundation of Markowitz mean-variance
optimization for a two-asset portfolio with weight `w` on asset 1 and
weight `1 - w` on asset 2.

## Definitions

* `mvPortfolioReturn` : expected return `w * r1 + (1 - w) * r2`
* `mvPortfolioVar`    : variance `w^2 * v1 + (1-w)^2 * v2 + 2*w*(1-w)*cov`
* `mvMinVarWeight`    : minimum-variance weight `(v2 - cov) / (v1 + v2 - 2*cov)`

## Main results

* `mvPortfolioReturn_equal_weight`          : equal-weight return is the arithmetic
  mean of the two asset returns
* `mvPortfolioVar_diversification_le`       : when `2*cov ≤ v1 + v2`, the portfolio
  variance is at most the convex combination of individual variances
* `mvPortfolioVar_diversification_lt`       : when `0 < w < 1` and `2*cov < v1 + v2`,
  diversification strictly reduces variance versus the weighted average
* `mvMinVarWeight_nonneg`                   : the minimum-variance weight is
  non-negative when `cov ≤ v2` and the denominator is positive
* `mvMinVarWeight_le_one`                   : the minimum-variance weight is at most 1
  when `cov ≤ v1` and the denominator is positive

The five results together cover the four items requested: portfolio return
definition, portfolio variance definition (simplified 2-asset case),
diversification reduces variance (two strength levels), equal-weight
return equals average, and minimum-variance weight bounded in [0, 1].

## Mathematical context

The diversification inequality rests on the identity

    mvPortfolioVar w v1 v2 cov - (w * v1 + (1 - w) * v2)
      = w * (w - 1) * v1 + (1 - w) * (1 - w - 1) * v2 + 2 * w * (1 - w) * cov
      = -w * (1 - w) * (v1 + v2 - 2 * cov).

For `0 ≤ w ≤ 1`, `w * (1 - w) ≥ 0`; so the sign of the difference is the
sign of `-(v1 + v2 - 2*cov)`. When `v1 + v2 ≥ 2*cov` (which follows from
the Cauchy-Schwarz / AM-GM bound when `cov = rho * sqrt(v1*v2)` and
`|rho| ≤ 1`) the difference is non-positive, giving the diversification
inequality. Strict inequality holds for interior weights.

## References

* Markowitz, H. "Portfolio Selection."
  *Journal of Finance* 7(1): 77-91 (1952).
* Merton, R. C. "An Analytic Derivation of the Efficient Portfolio
  Frontier." *Journal of Financial and Quantitative Analysis* 7(4):
  1851-1872 (1972).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

-- ---------------------------------------------------------------------------
-- Definitions
-- ---------------------------------------------------------------------------

/-- Expected return of a two-asset portfolio: `w * r1 + (1 - w) * r2`,
where `w` is the weight on asset 1. -/
noncomputable def mvPortfolioReturn (w r1 r2 : ℝ) : ℝ :=
  w * r1 + (1 - w) * r2

/-- Variance of a two-asset portfolio in covariance form:

    w^2 * v1 + (1 - w)^2 * v2 + 2 * w * (1 - w) * cov

where `v1, v2 ≥ 0` are individual variances and `cov` is the
covariance between the two assets. -/
noncomputable def mvPortfolioVar (w v1 v2 cov : ℝ) : ℝ :=
  w ^ 2 * v1 + (1 - w) ^ 2 * v2 + 2 * w * (1 - w) * cov

/-- Minimum-variance weight on asset 1:

    w* = (v2 - cov) / (v1 + v2 - 2 * cov)

This is the closed-form solution to the unconstrained two-asset
variance minimisation problem. -/
noncomputable def mvMinVarWeight (v1 v2 cov : ℝ) : ℝ :=
  (v2 - cov) / (v1 + v2 - 2 * cov)

-- ---------------------------------------------------------------------------
-- Theorem 1: equal-weight portfolio return is the arithmetic mean
-- ---------------------------------------------------------------------------

/-- **Equal-weight return equals the arithmetic mean.**
A portfolio with equal weights `w = 1/2` on both assets has expected
return equal to the arithmetic average of the two asset returns. -/
@[stat_lemma]
theorem mvPortfolioReturn_equal_weight (r1 r2 : ℝ) :
    mvPortfolioReturn (1 / 2) r1 r2 = (r1 + r2) / 2 := by
  unfold mvPortfolioReturn; ring

-- ---------------------------------------------------------------------------
-- Theorem 2: diversification weakly reduces variance (correlation ≤ 1)
-- ---------------------------------------------------------------------------

/-- **Diversification reduces variance (non-strict).**
When the covariance satisfies `2 * cov ≤ v1 + v2` — which follows from
the Cauchy-Schwarz / AM-GM condition `cov ≤ sqrt(v1 * v2) ≤ (v1 + v2) / 2`
whenever `|rho| ≤ 1` — the two-asset portfolio variance is at most the
convex combination of individual variances:

    mvPortfolioVar w v1 v2 cov ≤ w * v1 + (1 - w) * v2.

The proof uses the identity
`mvPortfolioVar w v1 v2 cov - (w * v1 + (1 - w) * v2) =
   -w * (1 - w) * (v1 + v2 - 2 * cov)`,
together with `w * (1 - w) ≥ 0` for `0 ≤ w ≤ 1`. -/
@[stat_lemma]
theorem mvPortfolioVar_diversification_le
    {w v1 v2 cov : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hcov : 2 * cov ≤ v1 + v2) :
    mvPortfolioVar w v1 v2 cov ≤ w * v1 + (1 - w) * v2 := by
  unfold mvPortfolioVar
  -- Suffices: w^2*v1 + (1-w)^2*v2 + 2*w*(1-w)*cov ≤ w*v1 + (1-w)*v2
  -- Rearranging: w*(w-1)*v1 + (1-w)*(-w)*v2 + 2*w*(1-w)*cov ≤ 0
  -- = -w*(1-w)*(v1+v2-2*cov) ≤ 0
  -- Since w*(1-w) ≥ 0 and v1+v2-2*cov ≥ 0, the product is nonneg.
  have hww : 0 ≤ w * (1 - w) := mul_nonneg hw0 (by linarith)
  have hdiff : 0 ≤ v1 + v2 - 2 * cov := by linarith
  nlinarith [mul_nonneg hww hdiff]

-- ---------------------------------------------------------------------------
-- Theorem 3: diversification strictly reduces variance (strict correlation)
-- ---------------------------------------------------------------------------

/-- **Diversification strictly reduces variance.**
For an interior weight `0 < w < 1` and strict covariance bound
`2 * cov < v1 + v2` (i.e. the two assets are not perfectly
positively correlated), the portfolio variance is strictly less than
the weighted average of individual variances:

    mvPortfolioVar w v1 v2 cov < w * v1 + (1 - w) * v2.

This is the core diversification benefit: blending two imperfectly
correlated assets strictly reduces variance versus the naive mix. -/
@[stat_lemma]
theorem mvPortfolioVar_diversification_lt
    {w v1 v2 cov : ℝ}
    (hw0 : 0 < w) (hw1 : w < 1)
    (hcov : 2 * cov < v1 + v2) :
    mvPortfolioVar w v1 v2 cov < w * v1 + (1 - w) * v2 := by
  unfold mvPortfolioVar
  have hww : 0 < w * (1 - w) := mul_pos hw0 (by linarith)
  have hdiff : 0 < v1 + v2 - 2 * cov := by linarith
  nlinarith [mul_pos hww hdiff]

-- ---------------------------------------------------------------------------
-- Theorem 4: minimum-variance weight is non-negative
-- ---------------------------------------------------------------------------

/-- **Minimum-variance weight is non-negative.**
When `cov ≤ v2` (so the numerator `v2 - cov ≥ 0`) and
`v1 + v2 > 2 * cov` (denominator positive), the minimum-variance
weight `w* = (v2 - cov) / (v1 + v2 - 2 * cov)` is non-negative. -/
@[stat_lemma]
theorem mvMinVarWeight_nonneg
    {v1 v2 cov : ℝ}
    (hnum : cov ≤ v2)
    (hdenom : 0 < v1 + v2 - 2 * cov) :
    0 ≤ mvMinVarWeight v1 v2 cov := by
  unfold mvMinVarWeight
  apply div_nonneg
  · linarith
  · linarith

-- ---------------------------------------------------------------------------
-- Theorem 5: minimum-variance weight is at most one
-- ---------------------------------------------------------------------------

/-- **Minimum-variance weight is at most one.**
When `cov ≤ v1` (numerator ≤ denominator) and
`v1 + v2 > 2 * cov` (denominator positive), the minimum-variance
weight `w* = (v2 - cov) / (v1 + v2 - 2 * cov)` is at most 1.

The key inequality is `v2 - cov ≤ v1 + v2 - 2 * cov`, which
simplifies to `cov ≤ v1`. -/
@[stat_lemma]
theorem mvMinVarWeight_le_one
    {v1 v2 cov : ℝ}
    (hnum_bound : cov ≤ v1)
    (hdenom : 0 < v1 + v2 - 2 * cov) :
    mvMinVarWeight v1 v2 cov ≤ 1 := by
  unfold mvMinVarWeight
  rw [div_le_one (by linarith)]
  linarith

end Pythia.Finance
