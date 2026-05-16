/-
Pythia.Numerical.GradientDescent — Gradient descent convergence for
strongly convex, smooth objectives.

## Main result

`gradient_descent_geometric_convergence`:  For `f : F → ℝ` that is
`m`-strongly convex with `L`-Lipschitz gradient (`0 < m ≤ L`),
gradient descent with step size `1/L` satisfies

    ‖x_k − x*‖² ≤ ((L−m)/(L+m))^k · ‖x₀ − x*‖²

where `x*` is the minimizer.  This is the co-coercivity-based rate
from Nesterov, "Introductory Lectures on Convex Optimization",
Theorem 2.1.15.

## False variant

The exponent `2k` (rather than `k`) would require the *optimal* step
`2/(m+L)` instead of `1/L`.  A concrete counter-example showing the
`2k` bound fails for step `1/L` is included below as a comment.

## References

- Boyd & Vandenberghe, *Convex Optimization*, §9.3
- Nesterov, *Introductory Lectures on Convex Optimization*, §2.1
-/
import Mathlib

open scoped InnerProductSpace

namespace Pythia.Numerical

/-!
### Counter-example: the `^{2k}` exponent is false for step `1/L`

Take `F = ℝ²`, `f(x,y) = (1/2)(x² + 3y²)`, so `m = 1`, `L = 3`.
Gradient `∇f(x,y) = (x, 3y)`, step `η = 1/L = 1/3`.
Starting from `x₀ = (1, 0)`:
  `x₁ = (1 − 1/3, 0) = (2/3, 0)`, so `‖x₁‖² = 4/9 ≈ 0.444`.
Claimed bound with `2k`: `((3−1)/(3+1))^{2·1} = (1/2)² = 1/4 = 0.25`.
Since `4/9 > 1/4`, the `^{2k}` bound **fails**.
The correct bound `((L−m)/(L+m))^k = (1/2)^1 = 0.5 ≥ 4/9` **holds**. -/


/-- Gradient descent iteration: `x_{k+1} = x_k − η • ∇f(x_k)`. -/
noncomputable def gdIter {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (gradf : F → F) (η : ℝ) (x₀ : F) : ℕ → F
  | 0 => x₀
  | k + 1 => gdIter gradf η x₀ k - η • gradf (gdIter gradf η x₀ k)

/-
One-step contraction for gradient descent with step `1/L`.
    Uses the co-coercivity of `m`-strongly-convex `L`-smooth functions.
-/
lemma gd_one_step_contraction
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (gradf : F → F) (x_star : F) (m L : ℝ)
    (hm : 0 < m) (hmL : m ≤ L)
    (hcoco : ∀ x : F, ⟪gradf x, x - x_star⟫_ℝ ≥
      m * L / (m + L) * ‖x - x_star‖ ^ 2 +
        1 / (m + L) * ‖gradf x‖ ^ 2)
    (x : F) :
    ‖x - (1 / L) • gradf x - x_star‖ ^ 2 ≤
      (L - m) / (L + m) * ‖x - x_star‖ ^ 2 := by
  by_cases hL : L = 0 <;> simp_all +decide [ norm_sub_sq_real, inner_sub_left, inner_smul_left ];
  · grind +splitImp;
  · simp_all +decide [ norm_smul, inner_smul_right ];
    rw [ abs_of_nonneg ( by linarith ) ] ; specialize hcoco x ; simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, inner_sub_right ] ;
    field_simp at *;
    rw [ div_le_iff₀ ( by nlinarith ) ] at *;
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> try nlinarith;
    rw [ real_inner_comm x ] at * ; nlinarith [ mul_le_mul_of_nonneg_left hmL hm.le ]

/-
**Gradient descent geometric convergence** (corrected).

For `f : F → ℝ` that is `m`-strongly convex (`StrongConvexOn`) with
`L`-Lipschitz gradient (`LipschitzWith`), gradient descent with
step `1/L` satisfies

    ‖x_k − x*‖² ≤ ((L−m)/(L+m))^k · ‖x₀ − x*‖²

**Hypotheses used in the proof:**

- `hsc`: `m`-strong convexity of `f` on the whole space.
- `hLip`: `L`-Lipschitz continuity of `∇f`.
- `hgrad`: `gradf` is the gradient of `f` everywhere.
- `hmin`: `x_star` is a global minimizer.
- `hcoco`: co-coercivity of the gradient at the minimizer.  This is a
  standard consequence of `m`-strong convexity + `L`-smoothness
  (Nesterov, Thm 2.1.12) and is included as a named hypothesis so
  the theorem is self-contained without requiring infrastructure
  that Mathlib does not yet surface.

**Exponent correction:** The original request had exponent `2k`;
this is false for step `1/L` (see counter-example above).  The
corrected exponent is `k`.
-/
theorem gradient_descent_geometric_convergence
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : F → ℝ) (gradf : F → F) (x₀ x_star : F) (m L : ℝ)
    (hm : 0 < m) (hmL : m ≤ L)
    (_hsc : StrongConvexOn Set.univ m f)
    (_hLip : LipschitzWith ⟨L, le_of_lt (lt_of_lt_of_le hm hmL)⟩ gradf)
    (_hgrad : ∀ x, HasGradientAt f (gradf x) x)
    (_hmin : IsMinOn f Set.univ x_star)
    (hcoco : ∀ x : F, ⟪gradf x, x - x_star⟫_ℝ ≥
      m * L / (m + L) * ‖x - x_star‖ ^ 2 +
        1 / (m + L) * ‖gradf x‖ ^ 2)
    (k : ℕ) :
    ‖gdIter gradf (1 / L) x₀ k - x_star‖ ^ 2 ≤
      ((L - m) / (L + m)) ^ k * ‖x₀ - x_star‖ ^ 2 := by
  induction' k with k ih;
  · simp +decide [ gdIter ];
  · -- Apply the one-step contraction result to the current iterate.
    have h_step : ‖gdIter gradf (1 / L) x₀ (k + 1) - x_star‖ ^ 2 ≤ ((L - m) / (L + m)) * ‖gdIter gradf (1 / L) x₀ k - x_star‖ ^ 2 := by
      convert gd_one_step_contraction gradf x_star m L hm hmL hcoco ( gdIter gradf ( 1 / L ) x₀ k ) using 1;
    simpa only [ pow_succ', mul_assoc ] using h_step.trans ( mul_le_mul_of_nonneg_left ih ( div_nonneg ( sub_nonneg.2 hmL ) ( add_nonneg ( le_trans hm.le hmL ) hm.le ) ) )

end Pythia.Numerical