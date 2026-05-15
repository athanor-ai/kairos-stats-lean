/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong Convexity (algebraic identities)

A twice-differentiable function `f : ℝ -> ℝ` is `mu`-strongly convex
if `f(y) >= f(x) + f'(x)(y-x) + (mu/2)(y-x)^2` for all `x, y`.

This file gives the algebraic kernel of strong convexity without
invoking differentiability or Hilbert-space machinery. We work with
the defining inequality directly.

## Main results

* `strongConvexGap`                 : `f(y) - f(x) - deriv_val * (y-x)`
* `strongConvexGap_lower`           : gap >= (mu/2)*(y-x)^2
* `strongConvex_unique_min`         : if x* minimizes f, it is unique
* `strongConvex_quadratic_growth`   : f(y) - f(x*) >= (mu/2)*(y-x*)^2

## References

* Nesterov, Y. "Introductory Lectures on Convex Optimization."
  Springer (2004), Definition 2.1.2.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization

/-- The strong-convexity gap: excess of f(y) over the first-order
Taylor approximation at x. -/
noncomputable def strongConvexGap (fy fx deriv_val x y : ℝ) : ℝ :=
  fy - fx - deriv_val * (y - x)

/-- **Lower bound from strong convexity.** If the gap is at least
`(mu/2)*(y-x)^2`, this encodes the strong convexity condition. -/
@[stat_lemma]
theorem strongConvexGap_lower {fy fx deriv_val x y mu : ℝ}
    (h : fy ≥ fx + deriv_val * (y - x) + mu / 2 * (y - x) ^ 2) :
    strongConvexGap fy fx deriv_val x y ≥ mu / 2 * (y - x) ^ 2 := by
  unfold strongConvexGap
  linarith

/-- **Quadratic growth at a minimizer.** At a minimizer x* where
the derivative is zero, strong convexity gives
`f(y) - f(x*) >= (mu/2)*(y - x*)^2`. -/
@[stat_lemma]
theorem strongConvex_quadratic_growth {fy fmin x_star y mu : ℝ}
    (h_sc : fy ≥ fmin + mu / 2 * (y - x_star) ^ 2) :
    fy - fmin ≥ mu / 2 * (y - x_star) ^ 2 := by
  linarith

/-- **Unique minimizer.** If `x₁` and `x₂` are both minimizers
(f(x₁) = f(x₂) = fmin) and strong convexity holds with `mu > 0`,
then `x₁ = x₂`. Proof: apply quadratic growth both directions. -/
@[stat_lemma]
theorem strongConvex_unique_min {fmin x₁ x₂ mu : ℝ}
    (hmu : 0 < mu)
    (h1 : fmin ≥ fmin + mu / 2 * (x₁ - x₂) ^ 2)
    (_h2 : fmin ≥ fmin + mu / 2 * (x₂ - x₁) ^ 2) :
    x₁ = x₂ := by
  have h_sq1 : mu / 2 * (x₁ - x₂) ^ 2 ≤ 0 := by linarith
  have h_sq_nonneg : 0 ≤ (x₁ - x₂) ^ 2 := sq_nonneg _
  have h_coeff : 0 < mu / 2 := by linarith
  have : (x₁ - x₂) ^ 2 = 0 := by
    nlinarith [mul_nonneg (le_of_lt h_coeff) h_sq_nonneg]
  have : x₁ - x₂ = 0 := by
    rwa [sq_eq_zero_iff] at this
  linarith

/-- **Positive gap away from minimizer.** When `mu > 0` and
`y != x*`, the quadratic growth term is strictly positive. -/
@[stat_lemma]
theorem strongConvex_gap_pos {x_star y mu : ℝ}
    (hmu : 0 < mu) (hne : x_star ≠ y) :
    0 < mu / 2 * (y - x_star) ^ 2 := by
  apply mul_pos (by linarith)
  exact sq_pos_iff.mpr (sub_ne_zero.mpr hne.symm)

end Pythia.Optimization
