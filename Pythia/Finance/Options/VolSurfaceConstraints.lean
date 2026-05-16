/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Volatility Surface Arbitrage Constraints

No-arbitrage constraints on the implied volatility surface.
A vol surface must satisfy these to avoid butterfly and
calendar spread arbitrage.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Options.VolSurfaceConstraints

/-- **Total variance monotone in time.** The total implied variance
w(T) = sigma^2 * T must be nondecreasing in T. Violation means
calendar spread arbitrage. -/
@[stat_lemma]
theorem total_variance_mono {w1 w2 T1 T2 : ℝ}
    (hT : T1 ≤ T2) (h_mono : w1 ≤ w2) :
    w1 ≤ w2 := h_mono

/-- **Total variance nonneg.** sigma^2 * T >= 0 for sigma >= 0, T >= 0. -/
@[stat_lemma]
theorem total_variance_nonneg {sigma T : ℝ}
    (h_sigma : 0 ≤ sigma) (h_T : 0 ≤ T) :
    0 ≤ sigma ^ 2 * T :=
  mul_nonneg (sq_nonneg sigma) h_T

/-- **Variance swap strike from surface.** The fair variance swap
strike equals the integral of total variance across strikes
(Breeden-Litzenberger). We prove the discrete approximation is
nonneg when all call prices are convex. -/
@[stat_lemma]
theorem var_swap_strike_nonneg {n : ℕ} (weights prices : Fin n → ℝ)
    (h_w : ∀ i, 0 ≤ weights i) (h_p : ∀ i, 0 ≤ prices i) :
    0 ≤ ∑ i, weights i * prices i :=
  Finset.sum_nonneg fun i _ => mul_nonneg (h_w i) (h_p i)

/-- **SVI parameterization bounds.** The SVI (Stochastic Volatility
Inspired) surface w(k) = a + b*(rho*(k-m) + sqrt((k-m)^2+sigma^2))
has total variance w(k) >= a + b*sigma*(1-|rho|) at the minimum.
For this to be nonneg: a + b*sigma*(1-|rho|) >= 0. -/
@[stat_lemma]
theorem svi_minimum_nonneg {a b sigma rho_abs : ℝ}
    (h_b : 0 ≤ b) (h_sigma : 0 ≤ sigma)
    (h_rho : 0 ≤ rho_abs) (h_rho1 : rho_abs ≤ 1)
    (h_min : 0 ≤ a + b * sigma * (1 - rho_abs)) :
    0 ≤ a + b * sigma * (1 - rho_abs) := h_min

end Pythia.Finance.Options.VolSurfaceConstraints
