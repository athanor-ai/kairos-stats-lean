/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markowitz Two-Asset Minimum-Variance Frontier

For two risky assets with variances `vX, vY > 0` and covariance `cXY`,
the *minimum-variance portfolio* — the long-only weighting on asset
1 that minimises total portfolio variance — has the closed form

    w*₁ = (vY - cXY) / (vX + vY - 2·cXY),

and the resulting minimum variance is

    vS* = (vX · vY - cXY²) / (vX + vY - 2·cXY).

This is the algebraic kernel of the Markowitz (1952) mean-variance
optimisation problem in the two-asset case.  The general n-asset
case requires inverting the covariance matrix; the two-asset case
collapses to the closed forms above.

This file gives the closed-form identities; the optimisation /
calculus link (`w*₁` minimises `portfolioVariance` at first-order
condition) is the natural follow-up but algebraically the closed
form is self-contained.

## Main results

* `minVarWeight1`           : `(vY - cXY) / (vX + vY - 2·cXY)`
* `minVarVariance`          : `(vX · vY - cXY²) / (vX + vY - 2·cXY)`
* `minVarVariance_nonneg`   : under PSD condition + denominator-positive,
  the minimum variance is non-negative
* `minVarWeight1_zero_corr` : at `cXY = 0`, the weight reduces to
  `vY / (vX + vY)` (inverse-variance weighting)

## Why this lemma

Two-asset Markowitz is the entry point to portfolio theory.  The
closed-form solution underpins pairs construction, hedge-ratio
selection (cousin of `Pythia.Finance.HedgeRatioMinVar`), and the
intuition behind multi-asset optimisation.  Surfacing the algebraic
identities in Pythia gives the `pythia` tactic cascade a clean
closure target for portfolio-construction sign/value goals.

## References

* Markowitz, H. "Portfolio Selection."
  *Journal of Finance* 7(1): 77-91 (1952).
* Merton, R. C. "An Analytic Derivation of the Efficient Portfolio
  Frontier." *Journal of Financial and Quantitative Analysis* 7(4):
  1851-1872 (1972).
-/
import Mathlib
import Pythia.Finance.Portfolio.PortfolioVariance
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Minimum-variance weight on asset 1 in a two-asset portfolio:
    `w*₁ = (vY - cXY) / (vX + vY - 2·cXY)`. -/
noncomputable def minVarWeight1 (vX vY cXY : ℝ) : ℝ :=
  (vY - cXY) / (vX + vY - 2 * cXY)

/-- Minimum variance achievable in a two-asset portfolio:
    `vS* = (vX · vY - cXY²) / (vX + vY - 2·cXY)`. -/
noncomputable def minVarVariance (vX vY cXY : ℝ) : ℝ :=
  (vX * vY - cXY^2) / (vX + vY - 2 * cXY)

/-- **Zero-correlation specialisation.** With `cXY = 0`, the
minimum-variance weight reduces to the *inverse-variance-weighting*
formula `vY / (vX + vY)` — the standard "more weight on the
less-volatile asset" rule. -/
@[stat_lemma]
theorem minVarWeight1_zero_corr (vX vY : ℝ) :
    minVarWeight1 vX vY 0 = vY / (vX + vY) := by
  unfold minVarWeight1; ring_nf

/-- **Minimum-variance non-negativity.** Under the positive-
semidefinite Cauchy-Schwarz condition `cXY² ≤ vX · vY` and the
denominator-positive condition `vX + vY > 2·cXY` (which holds
whenever `cXY < (vX + vY)/2`, e.g. when `cXY ≤ 0` or when both
variances dominate the cross-term), the minimum variance is
non-negative. -/
@[stat_lemma]
theorem minVarVariance_nonneg
    {vX vY cXY : ℝ} (hPSD : cXY^2 ≤ vX * vY)
    (hDenom : 0 < vX + vY - 2 * cXY) :
    0 ≤ minVarVariance vX vY cXY := by
  unfold minVarVariance
  apply div_nonneg
  · linarith
  · exact hDenom.le

end Pythia.Finance
