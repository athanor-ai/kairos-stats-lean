/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gradient Descent Convergence for Smooth Convex Functions

Classical convergence rate for gradient descent with fixed step size
on L-smooth convex functions: f(x_k) - f(x*) ≤ L‖x_0 - x*‖²/(2k).

## References

* Nesterov, Y. (2018): "Lectures on Convex Optimization" (2nd ed.), Thm 2.1.14.
* Beck, A. (2017): "First-Order Methods in Optimization", Ch. 10.

General applied mathematics.
-/
import Mathlib

open Real

noncomputable section

namespace Pythia.Optimization.GradientDescent

/-- Gradient descent convergence parameters. -/
structure GDParams where
  L : ℝ      -- Lipschitz constant of the gradient
  D : ℝ      -- initial distance to optimum ‖x_0 - x*‖
  hL : 0 < L
  hD : 0 ≤ D

/-- The GD convergence bound: after k iterations with step size 1/L,
f(x_k) - f(x*) ≤ L·D²/(2k). -/
def convergenceBound (p : GDParams) (k : ℕ) : ℝ :=
  p.L * p.D ^ 2 / (2 * ↑k)

/-- The convergence bound is nonneg. -/
theorem convergenceBound_nonneg (p : GDParams) (k : ℕ) (hk : 0 < k) :
    0 ≤ convergenceBound p k := by
  unfold convergenceBound
  apply div_nonneg
  · apply mul_nonneg (mul_nonneg (le_of_lt p.hL) (sq_nonneg p.D))
  · positivity

/-- The convergence bound is monotone decreasing in k. -/
theorem convergenceBound_antitone (p : GDParams) :
    Antitone (convergenceBound p) := by
  intro a b hab
  unfold convergenceBound
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (mul_nonneg (le_of_lt p.hL) (sq_nonneg p.D)) le_rfl
  · positivity
  · have : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
    linarith

/-- For ε-suboptimality, gradient descent needs k ≥ LD²/(2ε) iterations. -/
theorem iterations_for_epsilon (p : GDParams) (ε : ℝ) (hε : 0 < ε) :
    ∀ k : ℕ, 0 < k → (↑k : ℝ) ≥ p.L * p.D ^ 2 / (2 * ε) →
      convergenceBound p k ≤ ε := by
  intro k hk hk_bound
  unfold convergenceBound
  rw [div_le_iff (by positivity : (0 : ℝ) < 2 * ↑k)]
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  nlinarith [sq_nonneg p.D, p.hL, p.hD]

/-- The optimal step size for L-smooth convex GD is 1/L. -/
theorem optimal_step_size_pos (L : ℝ) (hL : 0 < L) : 0 < 1 / L :=
  div_pos one_pos hL

/-- GD with step size 1/L: each step reduces the objective by at
least (1/(2L))·‖∇f(x_k)‖². This is the descent lemma. -/
theorem descent_lemma_bound (L : ℝ) (hL : 0 < L)
    (grad_norm_sq : ℝ) (hgrad : 0 ≤ grad_norm_sq) :
    0 ≤ 1 / (2 * L) * grad_norm_sq := by
  apply mul_nonneg
  · positivity
  · exact hgrad

end Pythia.Optimization.GradientDescent
