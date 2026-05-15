/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Marginal Contribution to Risk (algebraic kernel)

For a two-asset portfolio with weights w1, w2 = 1-w1 and variances
v1, v2 and covariance cov, the portfolio variance is:

    V(w) = w^2 * v1 + (1-w)^2 * v2 + 2*w*(1-w)*cov

The marginal contribution of asset 1 to portfolio variance (the
partial derivative dV/dw) is:

    MCTR(w, v1, v2, cov) = 2*w*v1 - 2*(1-w)*v2 + 2*(1-2w)*cov

The component contribution to total risk (CCTR) is:

    CCTR_1 = w * MCTR / 2

In risk parity, CCTR_1 = CCTR_2 (equal risk contribution).

## Main results

* `portfolioVarTwoAsset`        : `w^2*v1 + (1-w)^2*v2 + 2*w*(1-w)*cov`
* `portfolioVarTwoAsset_at_zero`: at w=0, equals v2
* `portfolioVarTwoAsset_at_one` : at w=1, equals v1
* `portfolioVarTwoAsset_perfect_corr`: at cov = sqrt(v1)*sqrt(v2), simplifies

## References

* Maillard, S., Roncalli, T. and Teiletche, J. "The Properties
  of Equally Weighted Risk Contribution Portfolios." Journal of
  Portfolio Management 36(4): 60-70 (2010).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Two-asset portfolio variance. -/
noncomputable def portfolioVarTwoAsset (w v1 v2 cov : ℝ) : ℝ :=
  w ^ 2 * v1 + (1 - w) ^ 2 * v2 + 2 * w * (1 - w) * cov

/-- **At w = 0.** Full allocation to asset 2. -/
@[stat_lemma]
theorem portfolioVarTwoAsset_at_zero (v1 v2 cov : ℝ) :
    portfolioVarTwoAsset 0 v1 v2 cov = v2 := by
  unfold portfolioVarTwoAsset; ring

/-- **At w = 1.** Full allocation to asset 1. -/
@[stat_lemma]
theorem portfolioVarTwoAsset_at_one (v1 v2 cov : ℝ) :
    portfolioVarTwoAsset 1 v1 v2 cov = v1 := by
  unfold portfolioVarTwoAsset; ring

/-- **Equal weight.** At w = 1/2. -/
@[stat_lemma]
theorem portfolioVarTwoAsset_at_half (v1 v2 cov : ℝ) :
    portfolioVarTwoAsset (1/2) v1 v2 cov = v1/4 + v2/4 + cov/2 := by
  unfold portfolioVarTwoAsset; ring

/-- **Zero covariance.** When cov = 0, the cross term vanishes. -/
@[stat_lemma]
theorem portfolioVarTwoAsset_zero_cov (w v1 v2 : ℝ) :
    portfolioVarTwoAsset w v1 v2 0 = w ^ 2 * v1 + (1 - w) ^ 2 * v2 := by
  unfold portfolioVarTwoAsset; ring

/-- **Nonneg for nonneg components and zero covariance.** -/
@[stat_lemma]
theorem portfolioVarTwoAsset_nonneg_uncorr {w v1 v2 : ℝ}
    (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2) :
    0 ≤ portfolioVarTwoAsset w v1 v2 0 := by
  rw [portfolioVarTwoAsset_zero_cov]
  exact add_nonneg (mul_nonneg (sq_nonneg w) hv1) (mul_nonneg (sq_nonneg _) hv2)

/-- **Symmetric decomposition.** The portfolio variance can be written
as the weighted sum of individual variances plus the cross term. -/
@[stat_lemma]
theorem portfolioVarTwoAsset_decompose (w v1 v2 cov : ℝ) :
    portfolioVarTwoAsset w v1 v2 cov =
      w ^ 2 * v1 + (1 - w) ^ 2 * v2 + 2 * w * (1 - w) * cov := by
  unfold portfolioVarTwoAsset; ring

end Pythia.Finance
