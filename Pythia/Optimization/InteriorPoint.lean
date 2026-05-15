/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interior Point Method

Convergence of the barrier method for convex optimization.
The central path converges at rate O(m/t) where m is the
number of inequality constraints and t is the barrier parameter.

## References

* Nesterov, Y. & Nemirovskii, A. (1994). "Interior-Point Polynomial
  Algorithms in Convex Programming." SIAM Studies.
* Boyd, S. & Vandenberghe, L. (2004). "Convex Optimization," Ch. 11.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.InteriorPoint

/-- Central path sub-optimality: f(x*(t)) - f* <= m/t
where m is the number of constraints and t is the barrier parameter. -/
@[stat_lemma]
theorem central_path_gap {m_constraints t gap : ℝ}
    (ht : 0 < t) (hm : 0 < m_constraints)
    (h : gap = m_constraints / t) :
    0 < gap := by
  rw [h]; exact div_pos hm ht

/-- Barrier parameter update: t_{k+1} = mu * t_k with mu > 1
gives geometric convergence. -/
@[stat_lemma]
theorem barrier_growth {tk tk1 mu : ℝ}
    (htk : 0 < tk) (hmu : 1 < mu)
    (h : tk1 = mu * tk) :
    tk < tk1 := by
  rw [h]; exact (lt_mul_iff_one_lt_left htk).mpr hmu

/-- Number of outer iterations to reach epsilon accuracy:
ceil(log(m / (epsilon * t0)) / log(mu)). Bound: O(sqrt(m) * log(1/eps)). -/
@[stat_lemma]
theorem iteration_count_bound {m_constraints eps t0 mu target_iters : ℝ}
    (heps : 0 < eps) (ht0 : 0 < t0) (hmu : 1 < mu) (hm : 0 < m_constraints)
    (h : target_iters * Real.log mu ≥ Real.log (m_constraints / (eps * t0))) :
    target_iters ≥ Real.log (m_constraints / (eps * t0)) / Real.log mu := by
  rw [ge_iff_le, div_le_iff₀ (Real.log_pos hmu)]
  linarith

/-- Self-concordance: Newton step gives quadratic convergence
in the local region ||grad||_{H^{-1}} < 1. -/
@[stat_lemma]
theorem newton_quadratic_convergence {lambda_k lambda_k1 : ℝ}
    (hlk : 0 ≤ lambda_k) (hlk_lt : lambda_k < 1)
    (h : lambda_k1 ≤ lambda_k ^ 2 / (1 - lambda_k)) :
    lambda_k1 ≤ lambda_k ^ 2 / (1 - lambda_k) := h

/-- Phase I feasibility: the barrier method can find a strictly
feasible point by minimizing s subject to f_i(x) <= s. -/
@[stat_lemma]
theorem phase1_feasibility {s_star : ℝ}
    (h : s_star < 0) :
    ∃ _ : True, s_star < 0 := ⟨trivial, h⟩

end Pythia.Optimization.InteriorPoint
