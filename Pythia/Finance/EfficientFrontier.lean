/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Two-Asset Efficient Frontier (Markowitz, 1952)

For two assets with expected returns `mu1, mu2 : ℝ`, variances `v1, v2 : ℝ`,
and covariance `cov : ℝ` (where `cov = rho * sqrt(v1) * sqrt(v2)` in the
full parametrisation), a portfolio with weight `w` on asset 1 (and `1 - w`
on asset 2) has:

    portfolioReturn w mu1 mu2 = w * mu1 + (1 - w) * mu2

    portfolioVar w v1 v2 cov = w^2 * v1 + (1 - w)^2 * v2 + 2 * w * (1 - w) * cov

Working directly with the covariance form avoids the square-root bookkeeping
present in the full correlation-parametrised expression; the Cauchy-Schwarz
condition `cov^2 ≤ v1 * v2` characterises validity.

## Main definitions

* `portfolioReturn` : expected return of the weighted portfolio
* `portfolioVar`    : variance of the weighted portfolio (covariance-parametrised)

## Main results

* `portfolioReturn_at_zero`         : weight 0 gives pure asset-2 return
* `portfolioReturn_at_one`          : weight 1 gives pure asset-1 return
* `portfolioReturn_linear`          : return is an affine interpolation
* `portfolioVar_at_zero`            : weight 0 gives pure asset-2 variance
* `portfolioVar_at_one`             : weight 1 gives pure asset-1 variance
* `portfolioVar_nonneg_uncorrelated`: zero covariance + non-negative variances
  implies non-negative portfolio variance for any weight

## References

* Markowitz, H. "Portfolio Selection."
  *Journal of Finance* 7(1): 77-91 (1952).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Expected return of a two-asset portfolio with weight `w` on asset 1
and weight `1 - w` on asset 2. -/
noncomputable def portfolioReturn (w mu1 mu2 : ℝ) : ℝ :=
  w * mu1 + (1 - w) * mu2

/-- Variance of a two-asset portfolio with weight `w` on asset 1, where
`v1, v2` are the individual asset variances and `cov` is the covariance
between the two assets (`cov = rho * sqrt(v1) * sqrt(v2)` in the
correlation-parametrised form). -/
noncomputable def portfolioVar (w v1 v2 cov : ℝ) : ℝ :=
  w^2 * v1 + (1 - w)^2 * v2 + 2 * w * (1 - w) * cov

/-- **Pure asset-2 return.** A portfolio with zero weight on asset 1
delivers asset 2's expected return. -/
@[stat_lemma]
theorem portfolioReturn_at_zero (mu1 mu2 : ℝ) :
    portfolioReturn 0 mu1 mu2 = mu2 := by
  unfold portfolioReturn; ring

/-- **Pure asset-1 return.** A portfolio with full weight on asset 1
delivers asset 1's expected return. -/
@[stat_lemma]
theorem portfolioReturn_at_one (mu1 mu2 : ℝ) :
    portfolioReturn 1 mu1 mu2 = mu1 := by
  unfold portfolioReturn; ring

/-- **Affine interpolation.** The portfolio return is an affine function
of `w`: it equals `mu2` when `w = 0` and scales linearly as `w` increases,
with slope `mu1 - mu2`. -/
@[stat_lemma]
theorem portfolioReturn_linear (w mu1 mu2 : ℝ) :
    portfolioReturn w mu1 mu2 = mu2 + w * (mu1 - mu2) := by
  unfold portfolioReturn; ring

/-- **Pure asset-2 variance.** A portfolio with zero weight on asset 1
has variance equal to asset 2's variance. -/
@[stat_lemma]
theorem portfolioVar_at_zero (v1 v2 cov : ℝ) :
    portfolioVar 0 v1 v2 cov = v2 := by
  unfold portfolioVar; ring

/-- **Pure asset-1 variance.** A portfolio with full weight on asset 1
has variance equal to asset 1's variance. -/
@[stat_lemma]
theorem portfolioVar_at_one (v1 v2 cov : ℝ) :
    portfolioVar 1 v1 v2 cov = v1 := by
  unfold portfolioVar; ring

/-- **Non-negativity under zero covariance.** When the two assets are
uncorrelated (`cov = 0`) and each asset has non-negative variance
(`v1 ≥ 0`, `v2 ≥ 0`), the portfolio variance is non-negative for any
weight `w`. The proof uses `add_nonneg`, `mul_nonneg`, and `sq_nonneg`. -/
@[stat_lemma]
theorem portfolioVar_nonneg_uncorrelated (w v1 v2 : ℝ)
    (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2) :
    0 ≤ portfolioVar w v1 v2 0 := by
  unfold portfolioVar
  simp only [mul_zero, add_zero]
  apply add_nonneg
  · exact mul_nonneg (sq_nonneg w) hv1
  · exact mul_nonneg (sq_nonneg (1 - w)) hv2

end Pythia.Finance
