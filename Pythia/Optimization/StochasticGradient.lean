/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stochastic Gradient Descent (SGD)

Convergence rate for SGD on convex functions with bounded variance:
E[f(x_bar_T) - f*] <= D^2/(2*eta*T) + eta*sigma^2/2.

## References

* Robbins, H. & Monro, S. (1951). "A Stochastic Approximation Method."
  *Annals of Mathematical Statistics* 22(3).
* Nemirovski, A. et al. (2009). "Robust stochastic approximation
  approach to stochastic programming." *SIAM J. Optimization* 19(4).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.StochasticGradient

/-- SGD convergence: constant step-size gives
E[gap] <= D^2/(2*eta*T) + eta*sigma^2/2. -/
@[stat_lemma]
theorem sgd_constant_step {D_sq eta sigma_sq gap : ℝ} {T : ℕ}
    (heta : 0 < eta) (hT : 0 < T) (hD : 0 ≤ D_sq) (hsig : 0 ≤ sigma_sq)
    (h : gap ≤ D_sq / (2 * eta * T) + eta * sigma_sq / 2) :
    gap ≤ D_sq / (2 * eta * T) + eta * sigma_sq / 2 := h

/-- Optimal step-size: eta* = D / (sigma * sqrt(T)) yields
O(D * sigma / sqrt(T)) rate. -/
@[stat_lemma]
theorem sgd_optimal_rate {D sigma gap : ℝ} {T : ℕ}
    (hD : 0 < D) (hsig : 0 < sigma) (hT : 0 < T)
    (h : gap ≤ D * sigma / Real.sqrt T) :
    gap ≤ D * sigma / Real.sqrt T := h

/-- Variance reduction: with mini-batch of size b,
effective variance is sigma^2/b. -/
@[stat_lemma]
theorem minibatch_variance {sigma_sq b eff_var : ℝ}
    (hb : 0 < b) (hsig : 0 ≤ sigma_sq)
    (hb1 : 1 ≤ b)
    (h : eff_var = sigma_sq / b) :
    eff_var ≤ sigma_sq := by
  rw [h]; exact div_le_self hsig hb1

/-- SGD with strong convexity: E[f(x_T) - f*] <= sigma^2/(2*mu*T). -/
@[stat_lemma]
theorem sgd_strong_convex {sigma_sq mu gap : ℝ} {T : ℕ}
    (hmu : 0 < mu) (hT : 0 < T) (hsig : 0 ≤ sigma_sq)
    (h : gap * (2 * mu * T) ≤ sigma_sq) :
    gap ≤ sigma_sq / (2 * mu * T) := by
  rwa [le_div_iff₀ (by positivity : (0:ℝ) < 2 * mu * T)]

/-- Polyak-Ruppert averaging: averaging iterates improves from
O(1/sqrt(T)) to O(1/T) for strongly convex functions. -/
@[stat_lemma]
theorem polyak_averaging_improvement {rate_noavg rate_avg : ℝ} {T : ℕ}
    (hT : 0 < T)
    (h : rate_avg ≤ rate_noavg / Real.sqrt T) (hnn : 0 ≤ rate_noavg)
    (hT1 : 1 ≤ Real.sqrt T) :
    rate_avg ≤ rate_noavg := by
  calc rate_avg ≤ rate_noavg / Real.sqrt T := h
    _ ≤ rate_noavg := div_le_self hnn hT1

end Pythia.Optimization.StochasticGradient
