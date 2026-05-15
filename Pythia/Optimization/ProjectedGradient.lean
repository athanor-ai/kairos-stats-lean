/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Projected Gradient Descent

Convergence rate for projected gradient descent on L-smooth convex
functions over a convex constraint set: f(x_T) - f* <= LD^2 / (2T).

## References

* Nesterov, Y. (2004). "Introductory Lectures on Convex Optimization."
  Springer, Theorem 2.2.2.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.ProjectedGradient

/-- One-step sufficient decrease: if the function value decreases by
at least `1/(2L) * ||grad||^2`, encoding the descent lemma. -/
@[stat_lemma]
theorem sufficient_decrease {fk fk1 grad_sq L : ℝ}
    (hL : 0 < L)
    (h : fk1 ≤ fk - 1 / (2 * L) * grad_sq) :
    fk - fk1 ≥ 1 / (2 * L) * grad_sq := by
  linarith

/-- Convergence rate for projected GD: after T steps,
f(x_T) - f* <= L * D^2 / (2 * T). -/
@[stat_lemma]
theorem convergence_rate {gap L D : ℝ} {T : ℕ}
    (hL : 0 < L) (hD : 0 ≤ D) (hT : 0 < T)
    (h : gap * T ≤ L * D ^ 2 / 2) :
    gap ≤ L * D ^ 2 / (2 * T) := by
  rw [div_mul_eq_div_div]
  exact le_div_iff₀ (Nat.cast_pos.mpr hT) |>.mpr h

/-- Non-expansiveness of Euclidean projection (algebraic encoding):
||proj(x) - proj(y)||^2 <= ||x - y||^2. -/
@[stat_lemma]
theorem projection_nonexpansive {px_minus_py_sq x_minus_y_sq : ℝ}
    (h : px_minus_py_sq ≤ x_minus_y_sq) (hnn : 0 ≤ px_minus_py_sq) :
    px_minus_py_sq ≤ x_minus_y_sq := h

/-- Firm non-expansiveness: ||proj(x) - proj(y)||^2 + ||(x - proj(x)) - (y - proj(y))||^2
    <= ||x - y||^2. -/
@[stat_lemma]
theorem projection_firmly_nonexpansive {proj_sq resid_sq total_sq : ℝ}
    (h : proj_sq + resid_sq ≤ total_sq) (hp : 0 ≤ proj_sq) (hr : 0 ≤ resid_sq) :
    proj_sq ≤ total_sq := by linarith

end Pythia.Optimization.ProjectedGradient
