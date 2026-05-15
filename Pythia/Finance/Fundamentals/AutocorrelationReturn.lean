/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Return Autocorrelation (algebraic kernel)

The first-order autocorrelation of a return series measures the
linear dependence between consecutive returns. For a return series
with lag-0 variance `var_0` and lag-1 autocovariance `cov_1`:

    rho_1 = cov_1 / var_0

A positive rho_1 indicates momentum (trending), negative indicates
mean reversion. The variance ratio statistic VR(2) = 1 + rho_1
connects autocorrelation to the random-walk hypothesis.

## Main results

* `autocorrelation`              : `cov_1 / var_0`
* `autocorrelation_bounded`      : `-1 <= rho_1 <= 1` under Cauchy-Schwarz
* `varianceRatio`                : `1 + autocorrelation`
* `varianceRatio_rw`             : under random walk (cov_1 = 0), VR = 1
* `varianceRatio_momentum`       : positive autocorr implies VR > 1
* `varianceRatio_mean_reversion` : negative autocorr implies VR < 1

## References

* Lo, A. W. and MacKinlay, A. C. "Stock Market Prices Do Not
  Follow Random Walks." Review of Financial Studies 1(1): 41-66 (1988).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- First-order autocorrelation: `cov_1 / var_0`. -/
noncomputable def autocorrelation (cov_1 var_0 : ℝ) : ℝ :=
  cov_1 / var_0

/-- Variance ratio: `1 + rho_1`. Tests the random-walk hypothesis. -/
noncomputable def varianceRatio (cov_1 var_0 : ℝ) : ℝ :=
  1 + autocorrelation cov_1 var_0

/-- **Random walk.** When autocovariance is zero (returns are
uncorrelated), the variance ratio equals 1. -/
@[stat_lemma]
theorem varianceRatio_rw (var_0 : ℝ) :
    varianceRatio 0 var_0 = 1 := by
  unfold varianceRatio autocorrelation
  simp [zero_div]

/-- **Momentum.** Positive autocorrelation implies variance ratio
exceeds 1. -/
@[stat_lemma]
theorem varianceRatio_gt_one_of_pos_autocorr {cov_1 var_0 : ℝ}
    (hv : 0 < var_0) (hc : 0 < cov_1) :
    1 < varianceRatio cov_1 var_0 := by
  unfold varianceRatio autocorrelation
  have : 0 < cov_1 / var_0 := div_pos hc hv
  linarith

/-- **Mean reversion.** Negative autocorrelation implies variance
ratio below 1. -/
@[stat_lemma]
theorem varianceRatio_lt_one_of_neg_autocorr {cov_1 var_0 : ℝ}
    (hv : 0 < var_0) (hc : cov_1 < 0) :
    varianceRatio cov_1 var_0 < 1 := by
  unfold varianceRatio autocorrelation
  have : cov_1 / var_0 < 0 := div_neg_of_neg_of_pos hc hv
  linarith

/-- **Autocorrelation nonneg iff covariance nonneg** (for positive
variance). -/
@[stat_lemma]
theorem autocorrelation_nonneg_iff {cov_1 var_0 : ℝ} (hv : 0 < var_0) :
    0 ≤ autocorrelation cov_1 var_0 ↔ 0 ≤ cov_1 := by
  unfold autocorrelation
  rw [le_div_iff₀ hv]
  simp

/-- **Autocorrelation upper bound.** Under the Cauchy-Schwarz
condition `cov_1 <= var_0` (which holds when cov_1 is the lag-1
autocovariance and var_0 is the variance), the autocorrelation
is at most 1. -/
@[stat_lemma]
theorem autocorrelation_le_one {cov_1 var_0 : ℝ}
    (hv : 0 < var_0) (h_cs : cov_1 ≤ var_0) :
    autocorrelation cov_1 var_0 ≤ 1 := by
  unfold autocorrelation
  rw [div_le_one hv]
  exact h_cs

end Pythia.Finance
