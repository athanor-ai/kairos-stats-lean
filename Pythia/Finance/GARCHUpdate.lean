/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GARCH(1,1) Variance Update + Stationarity Condition

The GARCH(1,1) model (Bollerslev 1986) updates conditional variance via

    σ²_t = ω + α · ε²_{t-1} + β · σ²_{t-1},

with non-negativity parameters `ω ≥ 0, α ≥ 0, β ≥ 0` and the
covariance-stationarity condition `α + β < 1`.  Under stationarity,
the unconditional variance is `σ²_∞ = ω / (1 - α - β)`.

This file gives the closed-form algebraic identities for the update
recursion and the stationary unconditional variance.  The
probabilistic / ergodic theorem linking the update to actual time-
series variance is deferred to a probability-tier module.

## Main results

* `garchUpdate`                       : `ω + α·ε² + β·σ²`
* `garchUpdate_nonneg`                : non-negativity preserved
* `garchStationaryVariance`           : `ω / (1 - α - β)`
* `garchStationaryVariance_pos`       : positive under `ω > 0`, stationarity
* `garchStationaryVariance_recurrence`: stationary variance satisfies
  the affine fixed-point equation `σ²_∞ = ω + (α+β)·σ²_∞`

## Why this lemma

GARCH models are the practitioner-default for intraday volatility
forecasting on equity-vol desks.  The stationarity condition
`α + β < 1` is mission-critical: violating it causes forecasts to
explode to infinity over multi-step horizons.  Surfacing the closed
forms in Pythia gives the `pythia` cascade a clean closure target
for vol-engine sanity checks.

## References

* Bollerslev, T. "Generalized Autoregressive Conditional
  Heteroskedasticity." *Journal of Econometrics* 31(3): 307-327 (1986).
* Engle, R. F. "Autoregressive Conditional Heteroskedasticity with
  Estimates of the Variance of United Kingdom Inflation."
  *Econometrica* 50(4): 987-1007 (1982).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- GARCH(1,1) conditional-variance update:
    `σ²_t = ω + α · ε²_{t-1} + β · σ²_{t-1}`.

Arguments: previous innovation `ε`, previous conditional variance
`σ²`, GARCH parameters `ω, α, β`. -/
noncomputable def garchUpdate (ω α β ε σ_sq : ℝ) : ℝ :=
  ω + α * ε^2 + β * σ_sq

/-- **Non-negativity preserved.** If all parameters and previous
variance are non-negative, the update is non-negative. -/
@[stat_lemma]
theorem garchUpdate_nonneg
    {ω α β σ_sq : ℝ} (hω : 0 ≤ ω) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hσ : 0 ≤ σ_sq)
    (ε : ℝ) :
    0 ≤ garchUpdate ω α β ε σ_sq := by
  unfold garchUpdate
  have h1 : 0 ≤ α * ε^2 := mul_nonneg hα (sq_nonneg _)
  have h2 : 0 ≤ β * σ_sq := mul_nonneg hβ hσ
  linarith

/-- Stationary unconditional variance under GARCH(1,1):
    `σ²_∞ = ω / (1 - α - β)`. -/
noncomputable def garchStationaryVariance (ω α β : ℝ) : ℝ :=
  ω / (1 - α - β)

/-- **Stationary variance is positive.** Under positive `ω` and the
covariance-stationarity condition `α + β < 1` (with `α, β ≥ 0`),
the stationary variance is strictly positive. -/
@[stat_lemma]
theorem garchStationaryVariance_pos
    {ω α β : ℝ} (hω : 0 < ω) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β < 1) :
    0 < garchStationaryVariance ω α β := by
  unfold garchStationaryVariance
  have h_denom : 0 < 1 - α - β := by linarith
  exact div_pos hω h_denom

/-- **Stationary unconditional-variance recurrence.** The stationary
variance satisfies the affine fixed-point equation

    σ²_∞ = ω + (α + β) · σ²_∞.

This is the algebraic characterisation of the GARCH(1,1)
unconditional variance: it is the unique solution to the
expectation-recursion `E[σ²_t] = ω + (α+β) · E[σ²_{t-1}]` under
covariance stationarity (`α + β < 1`). -/
@[stat_lemma]
theorem garchStationaryVariance_recurrence
    {ω α β : ℝ} (hαβ : α + β < 1) :
    garchStationaryVariance ω α β = ω + (α + β) * garchStationaryVariance ω α β := by
  unfold garchStationaryVariance
  have h_denom : (1 - α - β) ≠ 0 := by
    intro h_eq
    linarith
  field_simp
  ring

end Pythia.Finance
