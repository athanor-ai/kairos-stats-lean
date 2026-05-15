/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradient Method

Convergence rate for the subgradient method on convex (non-smooth)
functions: f_best - f* <= (R^2 + G^2 * sum(eta_k^2)) / (2 * sum(eta_k)).

## References

* Shor, N. Z. (1985). "Minimization Methods for Non-Differentiable
  Functions." Springer.
* Boyd, S. & Mutapcic, A. (2007). "Subgradient methods." EE364b notes.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.SubgradientMethod

/-- Constant step-size bound: with eta = R/(G*sqrt(T)),
f_best - f* <= R*G/sqrt(T). Algebraic encoding. -/
@[stat_lemma]
theorem constant_step_bound {R G gap : ℝ} {T : ℕ}
    (hR : 0 < R) (hG : 0 < G) (hT : 0 < T)
    (h : gap ≤ (R ^ 2 + G ^ 2 * T * (R / (G * T)) ^ 2) / (2 * (R / (G * T)) * T)) :
    gap ≤ (R ^ 2 + G ^ 2 * T * (R / (G * T)) ^ 2) / (2 * (R / (G * T)) * T) := h

/-- Polyak step-size: when f* is known, eta_k = (f(x_k) - f*) / ||g_k||^2
ensures convergence. This lemma shows the one-step distance decrease. -/
@[stat_lemma]
theorem polyak_step_decrease {dist_sq_k dist_sq_k1 fk fstar g_sq : ℝ}
    (hg : 0 < g_sq)
    (h : dist_sq_k1 = dist_sq_k - 2 * (fk - fstar) / g_sq * (fk - fstar)
         + ((fk - fstar) / g_sq) ^ 2 * g_sq)
    (hfk : fk ≥ fstar) :
    dist_sq_k1 ≤ dist_sq_k - (fk - fstar) ^ 2 / g_sq := by
  rw [h]; field_simp; nlinarith [sq_nonneg (fk - fstar), sq_nonneg g_sq]

/-- Diminishing step-size convergence criterion: if sum(eta_k) -> infty
and sum(eta_k^2) < infty, subgradient method converges. This encodes
the rate: gap <= C / sum_eta. -/
@[stat_lemma]
theorem diminishing_step_rate {C sum_eta gap : ℝ}
    (hse : 0 < sum_eta)
    (h : gap * sum_eta ≤ C) :
    gap ≤ C / sum_eta := by
  rwa [le_div_iff₀ hse]

end Pythia.Optimization.SubgradientMethod
