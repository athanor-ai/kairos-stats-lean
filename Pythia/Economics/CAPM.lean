/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CAPM Beta Sign

The CAPM (Capital Asset Pricing Model) beta of asset i is defined as

  `beta_i = Cov(R_i, R_m) / Var(R_m)`

where `R_i` is the return of asset i, `R_m` is the market return,
`Cov(R_i, R_m)` is the covariance of asset i with the market, and
`Var(R_m) > 0` is the market return variance.

## Main results

* `capmBeta`           : the beta function `cov / varM`
* `capm_beta_nonneg`   : `beta_i >= 0` whenever `Cov(R_i, R_m) >= 0` and `Var(R_m) > 0`

## Why this lemma

Mathlib has `div_nonneg` and related real-division lemmas but no named
`capm` or `capmBeta` declaration. Pythia exposes the CAPM beta and its
nonnegativity so the `pythia` tactic cascade can close asset-pricing
goals without the user reaching for the underlying division lemmas.

The companion empirical layer (`tools/sim/economics_capm.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the bound holds across realistic
covariance and variance parameter ranges.

## References

* Sharpe, W. F. "Capital Asset Prices: A Theory of Market Equilibrium
  under Conditions of Risk." *Journal of Finance* 19(3): 425-442 (1964).
* Lintner, J. "The Valuation of Risk Assets and the Selection of Risky
  Investments in Stock Portfolios and Capital Budgets."
  *Review of Economics and Statistics* 47(1): 13-37 (1965).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Economics

/-- The CAPM beta of asset i: `cov(R_i, R_m) / var(R_m)`.
The arguments are unconstrained reals; the meaningful domain is
`varM > 0` (market variance strictly positive). -/
noncomputable def capmBeta (cov varM : ℝ) : ℝ := cov / varM

/-- **CAPM beta nonnegativity.** When the covariance of asset i with
the market is nonnegative and the market variance is strictly positive,
the CAPM beta is nonnegative. This captures the intuition that assets
which move with the market carry nonnegative systematic risk. -/
@[stat_lemma]
theorem capm_beta_nonneg {cov varM : ℝ} (hcov : 0 ≤ cov) (hvarM : 0 < varM) :
    0 ≤ capmBeta cov varM := by
  unfold capmBeta
  exact div_nonneg hcov hvarM.le

end Pythia.Economics
