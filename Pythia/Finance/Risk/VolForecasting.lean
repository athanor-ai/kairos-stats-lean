/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Volatility Forecasting Properties

EWMA and GARCH volatility forecast properties: mean reversion,
persistence, and forecast error bounds.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Risk.VolForecasting

/-- EWMA variance forecast: sigma^2_{t+1} = lambda*sigma^2_t + (1-lambda)*r^2_t. -/
noncomputable def ewmaVariance (lam sigma_sq r_sq : ℝ) : ℝ :=
  lam * sigma_sq + (1 - lam) * r_sq

/-- **EWMA is convex combination.** For lambda in [0,1], EWMA is
between sigma_sq and r_sq. -/
@[stat_lemma]
theorem ewma_between {lam sigma_sq r_sq : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (h : sigma_sq ≤ r_sq) :
    sigma_sq ≤ ewmaVariance lam sigma_sq r_sq := by
  unfold ewmaVariance
  linarith [mul_nonneg (by linarith : 0 ≤ 1 - lam) (by linarith : 0 ≤ r_sq - sigma_sq)]

/-- **EWMA nonneg.** Variance forecast is nonneg for nonneg inputs. -/
@[stat_lemma]
theorem ewma_nonneg {lam sigma_sq r_sq : ℝ}
    (hl : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hs : 0 ≤ sigma_sq) (hr : 0 ≤ r_sq) :
    0 ≤ ewmaVariance lam sigma_sq r_sq :=
  add_nonneg (mul_nonneg hl hs) (mul_nonneg (by linarith) hr)

/-- **Higher lambda = more persistence.** Lambda controls how much
weight goes to the previous forecast vs the new observation. -/
@[stat_lemma]
theorem ewma_persistence {sigma_sq r_sq : ℝ}
    (h : r_sq ≤ sigma_sq)
    {lam₁ lam₂ : ℝ} (hl : lam₁ ≤ lam₂) (hl1 : lam₂ ≤ 1) (hl0 : 0 ≤ lam₁) :
    ewmaVariance lam₁ sigma_sq r_sq ≤ ewmaVariance lam₂ sigma_sq r_sq := by
  unfold ewmaVariance
  nlinarith

/-- **GARCH(1,1) stationarity.** The unconditional variance is
sigma_bar^2 = omega / (1 - alpha - beta) when alpha + beta < 1. -/
@[stat_lemma]
theorem garch_unconditional_pos {omega alpha beta : ℝ}
    (h_omega : 0 < omega) (h_persist : alpha + beta < 1)
    (h_alpha : 0 ≤ alpha) (h_beta : 0 ≤ beta) :
    0 < omega / (1 - alpha - beta) :=
  div_pos h_omega (by linarith)

end Pythia.Finance.Risk.VolForecasting
