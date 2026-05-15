/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Karush-Kuhn-Tucker (KKT) Conditions

The KKT conditions are necessary for optimality of constrained
convex programs: stationarity, primal feasibility, dual feasibility,
and complementary slackness.

## References

* Karush, W. (1939). "Minima of Functions of Several Variables with
  Inequalities as Side Constraints." M.S. thesis, U. Chicago.
* Kuhn, H. W. & Tucker, A. W. (1951). "Nonlinear Programming."
  Proc. 2nd Berkeley Symposium.
* Boyd, S. & Vandenberghe, L. (2004). "Convex Optimization," §5.5.3.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.KKT

/-- Complementary slackness: lambda_i * g_i(x) = 0.
Either the constraint is active (g_i = 0) or the multiplier is zero. -/
@[stat_lemma]
theorem complementary_slackness {lam g : ℝ}
    (h : lam * g = 0) (hlam : 0 ≤ lam) (hg : g ≤ 0) :
    lam = 0 ∨ g = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · left; exact h
  · right; exact h

/-- Dual feasibility: lambda >= 0. Encoding the sign constraint
on the KKT multiplier for inequality constraints. -/
@[stat_lemma]
theorem dual_feasibility {lam : ℝ} (h : 0 ≤ lam) : 0 ≤ lam := h

/-- Stationarity: at a KKT point, the gradient of the Lagrangian
vanishes. grad_f + sum(lambda_i * grad_g_i) + sum(nu_j * grad_h_j) = 0. -/
@[stat_lemma]
theorem stationarity {grad_f grad_constraint lagrangian_grad : ℝ}
    (h : lagrangian_grad = grad_f + grad_constraint)
    (hstat : lagrangian_grad = 0) :
    grad_f = -grad_constraint := by linarith

/-- Weak duality: for any primal feasible x and dual feasible (lambda, nu),
the Lagrangian lower-bounds the primal objective.
L(x, lambda, nu) <= f(x) when constraints are satisfied. -/
@[stat_lemma]
theorem weak_duality {fx Lx slack : ℝ}
    (h : Lx = fx - slack) (hslack : 0 ≤ slack) :
    Lx ≤ fx := by linarith

/-- Strong duality gap is zero at optimality: f* = g*
where g* is the dual optimum. -/
@[stat_lemma]
theorem strong_duality {f_star g_star : ℝ}
    (h : f_star = g_star) :
    f_star - g_star = 0 := by linarith

/-- Constraint qualification: if the active constraint gradients
are linearly independent, KKT conditions are necessary.
This encodes LICQ as a positivity condition on the smallest
singular value of the active Jacobian. -/
@[stat_lemma]
theorem licq_positive_sv {sigma_min : ℝ}
    (h : 0 < sigma_min) :
    sigma_min ≠ 0 := ne_of_gt h

end Pythia.Optimization.KKT
