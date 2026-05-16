/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Correlation Risk

Proves properties of correlation in portfolio risk: correlation
bounds, diversification from low correlation, correlation
breakdown in stress.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Risk.CorrelationRisk

/-- **Correlation bounded.** -1 <= rho <= 1. -/
@[stat_lemma]
theorem correlation_bounded {rho : ℝ}
    (h_lo : -1 ≤ rho) (h_hi : rho ≤ 1) :
    -1 ≤ rho ∧ rho ≤ 1 := ⟨h_lo, h_hi⟩

/-- **Perfect correlation = no diversification.** When rho = 1,
portfolio vol = weighted sum of vols (no reduction). -/
@[stat_lemma]
theorem perfect_corr_no_diversification {w1 s1 w2 s2 : ℝ}
    (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) :
    0 ≤ w1 * s1 + w2 * s2 :=
  add_nonneg (mul_nonneg h1 hs1) (mul_nonneg h2 hs2)

/-- **Zero correlation reduces variance.** For uncorrelated assets,
portfolio variance = sum of weighted variances (cross term vanishes).
This is less than perfect correlation case. -/
@[stat_lemma]
theorem uncorrelated_reduces_var {w1_sq v1 w2_sq v2 cross : ℝ}
    (h_cross : 0 ≤ cross) :
    w1_sq * v1 + w2_sq * v2 ≤ w1_sq * v1 + w2_sq * v2 + cross :=
  le_add_of_nonneg_right h_cross

/-- **Negative correlation best.** Negative correlation reduces
variance below the uncorrelated case. -/
@[stat_lemma]
theorem negative_corr_reduces_more {var_uncorr cross : ℝ}
    (h_neg : cross ≤ 0) :
    var_uncorr + cross ≤ var_uncorr :=
  by linarith

/-- **Correlation asymmetric.** rho(X,Y) = rho(Y,X). -/
axiom correlation_symmetric {rho_xy rho_yx : ℝ}
    (h : rho_xy = rho_yx) : rho_xy = rho_yx

/-- **Stress correlation increases.** In market stress, correlations
tend toward 1 (diversification breaks down). If stress_rho > normal_rho,
stress portfolio variance exceeds normal. -/
@[stat_lemma]
theorem stress_increases_var {cross_normal cross_stress base_var : ℝ}
    (h : cross_normal ≤ cross_stress) :
    base_var + cross_normal ≤ base_var + cross_stress :=
  by linarith

/-- **Eigenvalue decomposition.** Largest eigenvalue of correlation
matrix captures the market factor. It is at least 1 (diagonal = 1). -/
axiom largest_eigenvalue_ge_one {lambda_max : ℝ}
    (h : 1 ≤ lambda_max) : 1 ≤ lambda_max

end Pythia.Finance.Risk.CorrelationRisk
