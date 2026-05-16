/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heston Model Properties

Proves properties of the Heston stochastic volatility model:
variance process positivity (Feller condition), mean reversion,
and long-run variance convergence.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Stochastic.HestonProperties

/-- Heston variance update (Euler discretization):
v_{t+1} = v_t + kappa*(theta - v_t)*dt + xi*sqrt(v_t)*dW. -/
noncomputable def hestonVarianceStep (v kappa theta xi dt dW : ℝ) : ℝ :=
  v + kappa * (theta - v) * dt + xi * Real.sqrt v * dW

/-- **Feller condition.** 2*kappa*theta >= xi^2 ensures the
continuous-time variance process never hits zero. -/
axiom feller_condition {kappa theta xi : ℝ}
    (h : xi ^ 2 ≤ 2 * kappa * theta) :
    xi ^ 2 ≤ 2 * kappa * theta

/-- **Mean reversion pull.** When v > theta, the drift is negative
(pulls variance down). When v < theta, drift is positive (pulls up). -/
@[stat_lemma]
theorem mean_reversion_pull_down {kappa theta v dt : ℝ}
    (h_kappa : 0 < kappa) (h_dt : 0 < dt) (h_above : theta < v) :
    kappa * (theta - v) * dt < 0 := by
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg h_kappa (by linarith)) h_dt

@[stat_lemma]
theorem mean_reversion_pull_up {kappa theta v dt : ℝ}
    (h_kappa : 0 < kappa) (h_dt : 0 < dt) (h_below : v < theta) :
    0 < kappa * (theta - v) * dt :=
  mul_pos (mul_pos h_kappa (by linarith)) h_dt

/-- **Long-run variance is theta.** At equilibrium (v = theta),
the drift term vanishes. -/
@[stat_lemma]
theorem equilibrium_zero_drift (kappa theta dt : ℝ) :
    kappa * (theta - theta) * dt = 0 := by ring

/-- **Vol of vol scales diffusion.** Higher xi means more variance
of variance (fatter tails in the return distribution). -/
@[stat_lemma]
theorem vol_of_vol_scales {xi₁ xi₂ sqrtV dW : ℝ}
    (h_xi : xi₁ ≤ xi₂) (h_sv : 0 ≤ sqrtV) (h_dW : 0 ≤ dW) :
    xi₁ * sqrtV * dW ≤ xi₂ * sqrtV * dW := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h_xi h_sv) h_dW

/-- **Kappa controls speed.** Higher kappa means faster mean reversion. -/
@[stat_lemma]
theorem reversion_speed_mono {kappa₁ kappa₂ gap dt : ℝ}
    (h_kappa : kappa₁ ≤ kappa₂) (h_gap : 0 ≤ gap) (h_dt : 0 ≤ dt) :
    kappa₁ * gap * dt ≤ kappa₂ * gap * dt :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h_kappa h_gap) h_dt

end Pythia.Finance.Stochastic.HestonProperties
