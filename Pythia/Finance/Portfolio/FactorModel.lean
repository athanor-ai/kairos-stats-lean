/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-Factor (CAPM-Style) Return Decomposition

The single-factor model decomposes an asset return into a systematic
component driven by a market factor and an idiosyncratic residual:

    r = alpha + beta * r_m + epsilon,

where `alpha` is the intercept (Jensen's alpha), `beta` is the market
sensitivity (CAPM beta), `r_m` is the market return, and `epsilon` is
the idiosyncratic residual.

Under the assumption that the residual is uncorrelated with the market
factor (`Cov(r_m, epsilon) = 0`), the total variance decomposes as

    Var(r) = beta^2 * Var(r_m) + Var(epsilon),

splitting into *systematic variance* `beta^2 * Var(r_m)` and
*idiosyncratic variance* `Var(epsilon)`.  The ratio of systematic
variance to total variance is the classical R-squared coefficient of
determination from the market regression.

## Main definitions

* `factorReturn`        : `alpha + beta * r_m + epsilon`
* `systematicVariance`  : `beta^2 * var_m`
* `totalVariance`       : `systematicVariance beta var_m + var_eps`

## Main results

* `factorReturn_at_zero_market`          : zero market return collapses to `alpha + epsilon`
* `factorReturn_at_zero_beta`            : zero beta collapses to `alpha + epsilon`
* `systematicVariance_nonneg`            : systematic variance is non-negative when `var_m >= 0`
* `totalVariance_ge_systematic`          : total variance dominates systematic variance when `var_eps >= 0`
* `systematicVariance_mono_beta_sq`      : systematic variance is monotone in `beta^2`
* `r_squared_decomposition`              : the R-squared ratio is non-negative when total variance is positive

## References

* Sharpe, W. F. "Capital Asset Prices: A Theory of Market Equilibrium
  under Conditions of Risk." *Journal of Finance* 19(3): 425-442 (1964).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Single-factor return: `r = alpha + beta * r_m + epsilon`, where
`alpha` is the intercept, `beta` is the market loading, `r_m` is the
market return, and `epsilon` is the idiosyncratic residual. -/
noncomputable def factorReturn (alpha beta r_m epsilon : ℝ) : ℝ :=
  alpha + beta * r_m + epsilon

/-- Systematic (market-factor) variance: `beta^2 * var_m`. -/
noncomputable def systematicVariance (beta var_m : ℝ) : ℝ :=
  beta ^ 2 * var_m

/-- Total variance under the single-factor model (assuming zero
covariance between the market factor and the idiosyncratic residual):
`beta^2 * var_m + var_eps`. -/
noncomputable def totalVariance (beta var_m var_eps : ℝ) : ℝ :=
  systematicVariance beta var_m + var_eps

/-- **Zero-market specialisation.** When the market return is zero,
the factor return collapses to `alpha + epsilon` (the intercept plus
the idiosyncratic residual). -/
@[stat_lemma]
theorem factorReturn_at_zero_market (alpha beta epsilon : ℝ) :
    factorReturn alpha beta 0 epsilon = alpha + epsilon := by
  unfold factorReturn; ring

/-- **Zero-beta specialisation.** A market-neutral asset (`beta = 0`)
has return equal to `alpha + epsilon`, carrying no systematic exposure
to the market factor. -/
@[stat_lemma]
theorem factorReturn_at_zero_beta (alpha r_m epsilon : ℝ) :
    factorReturn alpha 0 r_m epsilon = alpha + epsilon := by
  unfold factorReturn; ring

/-- **Non-negativity of systematic variance.** When the market
variance `var_m` is non-negative, the systematic variance
`beta^2 * var_m` is non-negative for any `beta`. The proof uses
`mul_nonneg` and `sq_nonneg`. -/
@[stat_lemma]
theorem systematicVariance_nonneg {var_m : ℝ} (hvm : 0 ≤ var_m) (beta : ℝ) :
    0 ≤ systematicVariance beta var_m := by
  unfold systematicVariance
  exact mul_nonneg (sq_nonneg beta) hvm

/-- **Total variance dominates systematic variance.** When the
idiosyncratic variance `var_eps` is non-negative, the total variance
is at least as large as the systematic variance. The proof uses
`le_add_of_nonneg_right`. -/
@[stat_lemma]
theorem totalVariance_ge_systematic {var_eps : ℝ} (hve : 0 ≤ var_eps)
    (beta var_m : ℝ) :
    systematicVariance beta var_m ≤ totalVariance beta var_m var_eps := by
  unfold totalVariance
  exact le_add_of_nonneg_right hve

/-- **Monotonicity of systematic variance in beta-squared.** If
`beta1^2 <= beta2^2` and `var_m >= 0`, then the systematic variance
at `beta1` is no greater than the systematic variance at `beta2`.
The proof uses `mul_le_mul_of_nonneg_right`. -/
@[stat_lemma]
theorem systematicVariance_mono_beta_sq {beta1 beta2 var_m : ℝ}
    (hb : beta1 ^ 2 ≤ beta2 ^ 2) (hvm : 0 ≤ var_m) :
    systematicVariance beta1 var_m ≤ systematicVariance beta2 var_m := by
  unfold systematicVariance
  exact mul_le_mul_of_nonneg_right hb hvm

/-- **R-squared non-negativity.** The R-squared coefficient of
determination, `systematicVariance beta var_m / totalVariance beta var_m var_eps`,
is non-negative when total variance is positive. The proof uses
`div_nonneg` together with `systematicVariance_nonneg`. -/
@[stat_lemma]
theorem r_squared_decomposition {beta var_m var_eps : ℝ}
    (hvm : 0 ≤ var_m)
    (htot : 0 < totalVariance beta var_m var_eps) :
    0 ≤ systematicVariance beta var_m / totalVariance beta var_m var_eps := by
  exact div_nonneg (systematicVariance_nonneg hvm beta) htot.le

end Pythia.Finance
