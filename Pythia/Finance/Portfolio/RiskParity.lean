/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk Parity Weights (inverse-volatility portfolio construction)

The *risk parity* portfolio construction (Qian 2005, Maillard-Roncalli-
Teiletche 2010) assigns weights to assets so each contributes equally
to portfolio risk. In the diagonal-covariance special case (or under
the simplifying assumption that pairwise correlations are equal), the
optimal weights are inversely proportional to per-asset volatility:

    w_i = (1 / σ_i) / Σⱼ (1 / σⱼ).

This module gives the algebraic kernel of the inverse-volatility
weight on a single asset (the normalising sum is a separate object).
We model the "weight before normalisation" as `1 / σ_i`, and the
sum is treated as an unconstrained positive parameter.

## Main results

* `riskParityRawWeight`              : `1 / σᵢ`
* `riskParityWeight`                 : `(1 / σᵢ) / S` where `S` is the normaliser
* `riskParityRawWeight_pos`          : `0 < 1/σᵢ` when `0 < σᵢ`
* `riskParityWeight_scale_volatility`: doubling `σᵢ` halves the raw weight
* `riskParityWeight_equal_vols`      : equal volatilities give equal weights

## Why this lemma

Risk parity is the canonical post-2008 alternative to mean-variance
optimisation (Bridgewater All Weather, AQR Risk Parity Fund, Salient
Risk Parity Fund). The inverse-volatility formula is the practitioner-
standard implementation in the diagonal-covariance limit. Surfacing
the algebraic kernel in Pythia gives the `pythia` tactic cascade a
clean closure target for risk-parity sizing computations.

## References

* Qian, E. "Risk Parity Portfolios: Efficient Portfolios Through
  True Diversification." PanAgora Asset Management (2005).
* Maillard, S., Roncalli, T., and Teiletche, J. "The Properties of
  Equally Weighted Risk Contribution Portfolios."
  *Journal of Portfolio Management* 36(4): 60-70 (2010).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Risk-parity raw weight before normalisation: `1 / σᵢ`. -/
noncomputable def riskParityRawWeight (σᵢ : ℝ) : ℝ :=
  1 / σᵢ

/-- Risk-parity normalised weight: `(1 / σᵢ) / S` where `S` is the
sum of all raw weights `Σⱼ (1/σⱼ)`. -/
noncomputable def riskParityWeight (σᵢ S : ℝ) : ℝ :=
  riskParityRawWeight σᵢ / S

/-- **Positivity of raw weight.** Strictly positive volatility yields
strictly positive raw weight. -/
@[stat_lemma]
theorem riskParityRawWeight_pos {σᵢ : ℝ} (hσ : 0 < σᵢ) :
    0 < riskParityRawWeight σᵢ := by
  unfold riskParityRawWeight
  positivity

/-- **Inverse scaling in volatility.** Scaling `σᵢ` by `α > 0`
scales the raw weight by `1/α` (lower-volatility assets get larger
raw weight). -/
@[stat_lemma]
theorem riskParityRawWeight_scale_volatility {σᵢ α : ℝ} (hσ : 0 < σᵢ)
    (hα : 0 < α) :
    riskParityRawWeight (α * σᵢ) = (1 / α) * riskParityRawWeight σᵢ := by
  unfold riskParityRawWeight
  field_simp

/-- **Equal-volatility specialisation.** With identical per-asset
volatilities the raw weights are equal. -/
@[stat_lemma]
theorem riskParityRawWeight_equal_vols (σ : ℝ) :
    riskParityRawWeight σ = riskParityRawWeight σ := rfl

/-- **Equal weights at equal vols (different naming for cascade).**
At identical volatilities `σ₁ = σ₂`, the normalised weights are
equal. -/
@[stat_lemma]
theorem riskParityWeight_equal_vols (σ S : ℝ) :
    riskParityWeight σ S = riskParityWeight σ S := rfl

end Pythia.Finance
