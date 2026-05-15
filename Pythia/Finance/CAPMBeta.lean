/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CAPM Beta (algebraic identities)

The Capital Asset Pricing Model beta is
`beta_i = Cov(R_i, R_m) / Var(R_m)`.
Expected return: `E[R_i] = R_f + beta_i * (E[R_m] - R_f)`.

## References

* Sharpe, W. F. (1964). "Capital Asset Prices." *Journal of Finance* 19(3).
* Lintner, J. (1965). "Security Prices, Risk, and Maximal Gains From
  Diversification." *Journal of Finance* 20(4).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.CAPMBeta

/-- CAPM expected return: E[R_i] = R_f + beta * (E[R_m] - R_f). -/
@[stat_lemma]
theorem capm_expected_return {Rf beta ERm ERi : ℝ}
    (h : ERi = Rf + beta * (ERm - Rf)) :
    ERi - Rf = beta * (ERm - Rf) := by
  linarith

/-- Beta decomposition: total risk = systematic + idiosyncratic.
Var(R_i) = beta^2 * Var(R_m) + Var(epsilon). -/
@[stat_lemma]
theorem risk_decomposition {var_i beta_sq var_m var_eps : ℝ}
    (h : var_i = beta_sq * var_m + var_eps)
    (heps : 0 ≤ var_eps) :
    beta_sq * var_m ≤ var_i := by
  linarith

/-- R-squared = systematic variance / total variance. -/
@[stat_lemma]
theorem r_squared_bound {beta_sq var_m var_i : ℝ}
    (hvi : 0 < var_i)
    (hle : beta_sq * var_m ≤ var_i)
    (hnn : 0 ≤ beta_sq * var_m) :
    beta_sq * var_m / var_i ≤ 1 := by
  rwa [div_le_one₀ hvi]

/-- Zero-beta portfolio has expected return = risk-free rate. -/
@[stat_lemma]
theorem zero_beta_return {Rf ERm ERi : ℝ}
    (h : ERi = Rf + 0 * (ERm - Rf)) :
    ERi = Rf := by
  simp at h; exact h

/-- Market portfolio has beta = 1. -/
@[stat_lemma]
theorem market_beta {Rf ERm : ℝ} :
    Rf + 1 * (ERm - Rf) = ERm := by ring

end Pythia.Finance.CAPMBeta
