/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Two-Asset Portfolio Variance (algebraic closed form)

For a portfolio with weights `α, β : ℝ` invested in two assets with
variances `vX, vY : ℝ` and covariance `cXY : ℝ`, the closed-form
portfolio variance is

    portfolioVariance α β vX vY cXY = α² · vX + 2·α·β · cXY + β² · vY.

This file gives the algebraic identity and its boundary / sign
properties.  The probabilistic link to `Var(αX + βY)` is established
separately in the probability-tier modules; here we expose the
closed-form computation that quant researchers reach for when sizing
two-asset portfolios.

## Main results

* `portfolioVariance`                     : closed form
* `portfolioVariance_zero_weights`        : zero weights → zero variance
* `portfolioVariance_full_in_one`         : `β = 0` → `α²·vX`
* `portfolioVariance_nonneg_for_psd`      : non-negative when the
  covariance matrix is positive semidefinite (Cauchy-Schwarz form)

## Why this lemma

Two-asset portfolio variance is the building block of mean-variance
optimisation, pairs-trading variance estimation, and hedge-ratio
calculation.  Quantitative practitioners use the closed form daily;
surfacing it in Pythia closes the gap between our matrix
concentration machinery (`Pythia.Frontier.MatrixBernstein`) and the
applied-portfolio language.

## References

* Markowitz, H. "Portfolio Selection."
  *Journal of Finance* 7(1): 77-91 (1952).
* Sharpe, W. F. "A Simplified Model for Portfolio Analysis."
  *Management Science* 9(2): 277-293 (1963).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Two-asset portfolio variance (algebraic form): given weights
`α, β` and variance/covariance triple `(vX, vY, cXY)`,

    portfolioVariance α β vX vY cXY = α² · vX + 2·α·β · cXY + β² · vY. -/
noncomputable def portfolioVariance (α β vX vY cXY : ℝ) : ℝ :=
  α^2 * vX + 2 * α * β * cXY + β^2 * vY

/-- **Zero weights.** A portfolio with zero allocation to both assets
has zero variance. -/
@[stat_lemma]
theorem portfolioVariance_zero_weights (vX vY cXY : ℝ) :
    portfolioVariance 0 0 vX vY cXY = 0 := by
  unfold portfolioVariance; ring

/-- **Single-asset specialisation.** With `β = 0`, the portfolio
variance reduces to `α² · vX`. -/
@[stat_lemma]
theorem portfolioVariance_full_in_one (α vX vY cXY : ℝ) :
    portfolioVariance α 0 vX vY cXY = α^2 * vX := by
  unfold portfolioVariance; ring

/-- **Non-negativity for PSD covariance.** When the covariance matrix
is positive semidefinite (i.e. `vX, vY ≥ 0` and the Cauchy-Schwarz
form `cXY² ≤ vX · vY` holds), the portfolio variance is non-negative
for any weights `α, β`.

The proof uses the standard PSD-form trick: write the quadratic in
`α, β` as a non-negative sum-of-squares using `vX·vY ≥ cXY²`. -/
@[stat_lemma]
theorem portfolioVariance_nonneg_for_psd
    {vX vY cXY : ℝ} (hvX : 0 ≤ vX) (hvY : 0 ≤ vY)
    (hCS : cXY^2 ≤ vX * vY) (α β : ℝ) :
    0 ≤ portfolioVariance α β vX vY cXY := by
  unfold portfolioVariance
  by_cases hvX0 : vX = 0
  · subst hvX0
    have hcXY_sq_le : cXY^2 ≤ 0 := by linarith [hCS]
    have hcXY_sq_nn : 0 ≤ cXY^2 := sq_nonneg cXY
    have hcXY : cXY = 0 := by
      have : cXY^2 = 0 := le_antisymm hcXY_sq_le hcXY_sq_nn
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    subst hcXY
    nlinarith [sq_nonneg β, hvY]
  · have hvX_pos : 0 < vX := lt_of_le_of_ne hvX (Ne.symm hvX0)
    have h_sq1 : 0 ≤ (α * vX + β * cXY)^2 := sq_nonneg _
    have h_sq2 : 0 ≤ β^2 := sq_nonneg β
    have h_pos_diff : 0 ≤ vX * vY - cXY^2 := by linarith
    have h_mul_nn : 0 ≤ β^2 * (vX * vY - cXY^2) := mul_nonneg h_sq2 h_pos_diff
    nlinarith [sq_nonneg (α * vX + β * cXY), h_pos_diff, sq_nonneg β]

end Pythia.Finance
