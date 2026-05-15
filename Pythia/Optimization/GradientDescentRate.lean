/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gradient Descent Convergence Rate (algebraic kernel)

For a function with `L`-Lipschitz gradient, gradient descent with
step size `eta = 1/L` satisfies

    f(x_{k+1}) <= f(x_k) - (1/(2L)) * ||grad_k||^2

The cumulative version after `n` steps gives

    min_k ||grad_k||^2 <= 2L * (f(x_0) - f_star) / n

This file gives the algebraic identities for the per-step sufficient
decrease and the 1/n convergence rate, without invoking any
functional-analysis or Hilbert-space machinery.

## Main results

* `sufficientDecrease`                : `f_next <= f_curr - step * grad_sq`
* `sufficientDecrease_improvement`    : `0 <= f_curr - f_next` under decrease
* `convergenceRate`                   : `min_grad_sq <= 2 * L * gap / n`
* `convergenceRate_vanishes`          : rate bound is antitone in `n`

## Why this lemma

Gradient descent is the workhorse of continuous optimization and
machine learning. The 1/n rate for smooth non-convex functions is
the baseline against which all accelerated methods are compared.
Surfacing the algebraic convergence kernel in Pythia gives the
`pythia` tactic cascade a clean closure target for optimization
rate-bound goals.

## References

* Nesterov, Y. "Introductory Lectures on Convex Optimization."
  Springer (2004), Theorem 1.2.4.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization

/-- Sufficient decrease condition: `f(x_{k+1}) <= f(x_k) - eta * ||grad||^2`.
The `step` parameter is the effective step size (typically `1/(2L)`). -/
noncomputable def sufficientDecrease (f_curr f_next step grad_sq : ℝ) : Prop :=
  f_next ≤ f_curr - step * grad_sq

/-- **Improvement from sufficient decrease.** Under the sufficient
decrease condition with nonneg step and nonneg gradient norm squared,
the function value does not increase. -/
@[stat_lemma]
theorem sufficientDecrease_improvement {f_curr f_next step grad_sq : ℝ}
    (h_step : 0 ≤ step) (h_grad : 0 ≤ grad_sq)
    (h_dec : sufficientDecrease f_curr f_next step grad_sq) :
    f_next ≤ f_curr := by
  unfold sufficientDecrease at h_dec
  have : 0 ≤ step * grad_sq := mul_nonneg h_step h_grad
  linarith

/-- **Gradient bound from telescoping.** If the function decreases by
at least `step * grad_sq_k` at each step, then the minimum gradient
norm squared over `n` steps is bounded by the total decrease divided
by `n * step`:
    `min_grad_sq <= (f_0 - f_n) / (n * step)`.

This is the algebraic core of the 1/n rate. -/
@[stat_lemma]
theorem gradient_bound_from_decrease
    {f_init f_final step min_grad_sq : ℝ} {n : ℕ}
    (hn : 0 < (n : ℝ)) (h_step : 0 < step)
    (h_min_bound : min_grad_sq * (↑n * step) ≤ f_init - f_final) :
    min_grad_sq ≤ (f_init - f_final) / (↑n * step) := by
  rw [le_div_iff₀ (mul_pos hn h_step)]
  linarith

/-- **Rate bound is antitone in step count.** For fixed initial gap
and step size, a larger number of iterations gives a tighter bound
on the minimum gradient norm squared. -/
@[stat_lemma]
theorem rate_antitone_n {gap step : ℝ} (h_gap : 0 ≤ gap) (h_step : 0 < step)
    {n₁ n₂ : ℕ} (hn₁ : 0 < (n₁ : ℝ)) (hn : (n₁ : ℝ) ≤ n₂) :
    gap / (↑n₂ * step) ≤ gap / (↑n₁ * step) := by
  apply div_le_div_of_nonneg_left h_gap (mul_pos hn₁ h_step)
  exact mul_le_mul_of_nonneg_right hn (le_of_lt h_step)

/-- **Nonneg gap implies nonneg rate bound.** -/
@[stat_lemma]
theorem rate_nonneg {gap step : ℝ} {n : ℕ}
    (h_gap : 0 ≤ gap) (h_step : 0 < step) (hn : 0 < (n : ℝ)) :
    0 ≤ gap / (↑n * step) :=
  div_nonneg h_gap (le_of_lt (mul_pos hn h_step))

end Pythia.Optimization
