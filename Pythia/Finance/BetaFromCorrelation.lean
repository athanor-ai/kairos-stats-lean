/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CAPM Beta via Correlation Identity

The CAPM *beta* of an asset is

    β = Cov(r_p, r_m) / Var(r_m)
      = ρ · σ_p / σ_m,

where `ρ` is the Pearson correlation between the asset and market
returns, and `σ_p`, `σ_m` are the respective return standard
deviations.  This identity (a corollary of `Cov = ρ · σ_p · σ_m` and
`Var = σ_m²`) is the practitioner-standard estimation form: regress
the asset against the market, or scale correlation by the volatility
ratio.

This module gives the algebraic kernel `β = ρ · σ_p / σ_m` treating
`ρ`, `σ_p`, `σ_m` as unconstrained real parameters; the underlying
probability link (`Cov`, `Var`) is deferred to a probability-tier
module.

## Main results

* `betaFromCorrelation`           : `ρ · σ_p / σ_m`
* `betaFromCorrelation_zero_corr` : `ρ = 0` ⇒ `β = 0` (uncorrelated)
* `betaFromCorrelation_unit_corr` : `ρ = 1` ⇒ `β = σ_p / σ_m` (perfectly correlated)
* `betaFromCorrelation_scale_p`   : scaling `σ_p` by `α` scales `β` by `α`

## Why this lemma

Beta is the *single* CAPM input that determines systematic-risk
exposure and feeds Treynor (`(r_p − r_f)/β`), Jensen's alpha
(`r_p − r_f − β(r_m − r_f)`), the SML, and every market-neutral
portfolio construction.  Surfacing the `β = ρσ_p/σ_m` algebraic
closed form in Pythia gives the `pythia` tactic cascade a clean
closure target for CAPM-decomposition computations.

## References

* Sharpe, W. F. "Capital Asset Prices: A Theory of Market
  Equilibrium under Conditions of Risk."
  *Journal of Finance* 19(3): 425-442 (1964).
* Lintner, J. "The Valuation of Risk Assets and the Selection of
  Risky Investments in Stock Portfolios and Capital Budgets."
  *Review of Economics and Statistics* 47(1): 13-37 (1965).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- CAPM beta via correlation: `β = ρ · σ_p / σ_m`. -/
noncomputable def betaFromCorrelation (ρ σp σm : ℝ) : ℝ :=
  ρ * σp / σm

/-- **Zero-correlation specialisation.** An asset uncorrelated with
the market has zero CAPM beta — it carries no systematic-risk
exposure. -/
@[stat_lemma]
theorem betaFromCorrelation_zero_corr (σp σm : ℝ) :
    betaFromCorrelation 0 σp σm = 0 := by
  unfold betaFromCorrelation; simp

/-- **Perfect-correlation specialisation.** A perfectly correlated
asset has beta equal to the volatility ratio `σ_p / σ_m`. -/
@[stat_lemma]
theorem betaFromCorrelation_unit_corr (σp σm : ℝ) :
    betaFromCorrelation 1 σp σm = σp / σm := by
  unfold betaFromCorrelation; simp

/-- **Scaling in portfolio volatility.** Scaling `σ_p` by `α`
scales the beta by `α`. -/
@[stat_lemma]
theorem betaFromCorrelation_scale_p (ρ α σp σm : ℝ) :
    betaFromCorrelation ρ (α * σp) σm = α * betaFromCorrelation ρ σp σm := by
  unfold betaFromCorrelation
  ring

end Pythia.Finance
