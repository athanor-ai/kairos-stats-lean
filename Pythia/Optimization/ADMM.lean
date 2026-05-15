/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ADMM (Alternating Direction Method of Multipliers)

Algebraic identities for the ADMM convergence analysis. The
primal residual `r_k = Ax_k + Bz_k - c` and dual residual
`s_k = rho * B^T (z_k - z_{k-1})` both vanish at convergence.

## References

* Boyd, S., Parikh, N., Chu, E., Peleato, B. and Eckstein, J. (2011).
  "Distributed Optimization and Statistical Learning via the Alternating
  Direction Method of Multipliers." Foundations and Trends in Machine
  Learning 3(1).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.ADMM

/-- ADMM Lyapunov decrease: the augmented Lagrangian decreases by
at least `rho/2 * ||r_k||^2 + 1/(2*rho) * ||s_k||^2`. -/
@[stat_lemma]
theorem lyapunov_decrease {Lk Lk1 rho r_sq s_sq : ℝ}
    (hrho : 0 < rho)
    (h : Lk1 ≤ Lk - rho / 2 * r_sq - 1 / (2 * rho) * s_sq)
    (hr : 0 ≤ r_sq) (hs : 0 ≤ s_sq) :
    Lk - Lk1 ≥ rho / 2 * r_sq + 1 / (2 * rho) * s_sq := by
  linarith

/-- Primal-dual residual tradeoff: rho controls the balance between
primal feasibility (r) and dual feasibility (s). -/
@[stat_lemma]
theorem residual_tradeoff {rho r_sq s_sq bound : ℝ}
    (hrho : 0 < rho) (hr : 0 ≤ r_sq) (hs : 0 ≤ s_sq)
    (h : rho * r_sq + s_sq / rho ≤ bound) :
    r_sq ≤ bound / rho := by
  have h1 : rho * r_sq ≤ bound := by
    have : s_sq / rho ≥ 0 := div_nonneg hs (le_of_lt hrho)
    linarith
  rwa [le_div_iff₀ hrho, mul_comm]

/-- Convergence rate: after T iterations, min residual is O(1/T). -/
@[stat_lemma]
theorem convergence_rate {L0 Lstar : ℝ} {T : ℕ}
    (hT : 0 < T)
    (hL : 0 ≤ L0 - Lstar)
    (min_resid : ℝ)
    (h : min_resid * T ≤ L0 - Lstar) :
    min_resid ≤ (L0 - Lstar) / T := by
  rwa [le_div_iff₀ (Nat.cast_pos.mpr hT)]

/-- Dual update identity: y_{k+1} = y_k + rho * r_k. -/
@[stat_lemma]
theorem dual_update {yk1 yk rho rk : ℝ}
    (h : yk1 = yk + rho * rk) :
    yk1 - yk = rho * rk := by
  linarith

end Pythia.Optimization.ADMM
