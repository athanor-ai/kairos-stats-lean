/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharpe-Ratio Bridge to Anytime-Valid Confidence Sequences

This file establishes the algebraic bridge between Pythia's existing
anytime-valid confidence-sequence infrastructure
(`Pythia.HowardRamdasCS`, `Pythia.VilleSupermartingale`,
`Pythia.SubGaussianMG`) and the Sharpe-ratio reporting language used
by quantitative researchers.

The core structural identity is *Lipschitz-in-mean*:

    sharpeRatio μ_hat rf σ - sharpeRatio μ_star rf σ = (μ_hat - μ_star) / σ.

Combined with any anytime-valid mean confidence sequence
`|μ_hat_t - μ_star| ≤ B_t`, this yields the anytime-valid Sharpe
confidence band

    |sharpeRatio μ_hat rf σ - sharpeRatio μ_star rf σ| ≤ B_t / σ.

The probabilistic ingredient (Howard-Ramdas / Ville bound on the mean)
already exists in Pythia; this file provides the *translation layer*
into Sharpe units that quantitative practitioners reach for.

## Main results

* `sharpe_diff_eq_excess_over_sigma`  : structural Sharpe identity
* `sharpe_lipschitz_in_mean`          : Lipschitz constant `1/σ` in mean
* `sharpe_cs_band`                    : translate mean CS into Sharpe CS

## Why this lemma

Quantitative practitioners constantly answer "is my signal real?"
by peeking at running Sharpe ratios.  Naive z-tests over-reject
under continuous monitoring; the *anytime-valid* confidence-sequence
shape provided by Ville / Howard-Ramdas is the correct discipline.
Pythia already has the underlying e-process / supermartingale
machinery — this file is the bridge that lets quantitative users
phrase the result in Sharpe-ratio language without redoing the
sub-Gaussian / sub-gamma derivation.

## References

* Howard, S. R., Ramdas, A., McAuliffe, J., and Sekhon, J.
  "Time-uniform Chernoff bounds via nonnegative supermartingales."
  *Probability Surveys* 17: 257-317 (2020).  (Anytime-valid CS.)
* Sharpe, W. F. "Mutual Fund Performance."
  *Journal of Business* 39(S1): 119-138 (1966).  (Sharpe ratio.)
-/
import Mathlib
import Pythia.Finance.Portfolio.SharpeRatio
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- **Structural Sharpe identity.** For any reals,

    sharpeRatio μ_hat rf σ - sharpeRatio μ_star rf σ = (μ_hat - μ_star) / σ. -/
@[stat_lemma]
theorem sharpe_diff_eq_excess_over_sigma (μ_hat μ_star rf σ : ℝ) :
    sharpeRatio μ_hat rf σ - sharpeRatio μ_star rf σ = (μ_hat - μ_star) / σ := by
  unfold sharpeRatio
  rw [← sub_div]
  congr 1
  ring

/-- **Lipschitz-in-mean.** For fixed positive volatility, the Sharpe
ratio is 1/σ-Lipschitz in the mean argument:

    |sharpeRatio μ_hat rf σ - sharpeRatio μ_star rf σ| = |μ_hat - μ_star| / σ. -/
@[stat_lemma]
theorem sharpe_lipschitz_in_mean {σ : ℝ} (hσ : 0 < σ) (μ_hat μ_star rf : ℝ) :
    |sharpeRatio μ_hat rf σ - sharpeRatio μ_star rf σ| = |μ_hat - μ_star| / σ := by
  rw [sharpe_diff_eq_excess_over_sigma, abs_div, abs_of_pos hσ]

/-- **CS bridge.** A confidence-sequence band `B` on the mean
translates into a confidence-sequence band `B / σ` on the Sharpe
ratio.  This is the operational bridge: any anytime-valid bound on
`|μ_hat_t - μ_star|` (e.g. from `Pythia.HowardRamdasCS` or the
Ville inequality in `Pythia.VilleSupermartingale`) yields an
anytime-valid bound on the Sharpe-ratio gap. -/
@[stat_lemma]
theorem sharpe_cs_band {σ B : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B)
    {μ_hat μ_star rf : ℝ} (h_cs : |μ_hat - μ_star| ≤ B) :
    |sharpeRatio μ_hat rf σ - sharpeRatio μ_star rf σ| ≤ B / σ := by
  rw [sharpe_lipschitz_in_mean hσ]
  exact div_le_div_of_nonneg_right h_cs hσ.le

end Pythia.Finance
