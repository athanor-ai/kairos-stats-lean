/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lagrangian Duality and Weak Duality

Formalizes the Lagrangian function, the dual function, and weak duality
for the constrained optimization program:

    minimize  f(x)
    subject to  g_i(x) <= 0,   i = 1, ..., m

The Lagrangian is:

    L(x, lambda) = f(x) + sum_{i=1}^{m} lambda_i * g_i(x)

The dual function is:

    d(lambda) = inf_x L(x, lambda)

## Main results

* `lagrangian_at_zero_multipliers` — when all multipliers are zero, the
  Lagrangian reduces to the objective: `L(x, 0) = f(x)`.

* `lagrangian_le_objective_at_feasible` — for any feasible point x (all
  g_i(x) <= 0) and nonneg multipliers (all lambda_i >= 0), the Lagrangian
  is at most the objective: `L(x, lambda) <= f(x)`.

* `weak_duality` — for any feasible x and nonneg lambda, any lower bound
  d on the Lagrangian satisfies `d <= f(x)`.

* `lagrangian_mono_multiplier` — when a constraint is tight at x (g_i(x) = 0),
  changing that multiplier does not change the Lagrangian value at x.

* `duality_gap_nonneg` — the duality gap `f(x) - d(lambda)` is nonneg for
  any feasible x, nonneg lambda, and lower bound d on the Lagrangian.

## Why this lemma

Weak duality is the foundational inequality of convex optimization: it
certifies a lower bound on the primal optimal value via a dual certificate,
without requiring convexity. Every duality-gap bound, KKT condition
argument, and interior-point convergence proof invokes weak duality at
its core. Surfacing the algebraic statement in Pythia gives the `pythia`
tactic cascade a clean closure target for optimization duality goals.

## References

* Boyd, S. and Vandenberghe, L. "Convex Optimization." Cambridge University
  Press (2004), Chapter 5.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization

/-! ### Definition: Lagrangian -/

/-- The Lagrangian for a single-variable constrained optimization program
with `m` inequality constraints.

    L(x, lambda) = f(x) + sum_i lambda_i * g_i(x)

The objective is `f : ℝ → ℝ`, the constraints are `g : Fin m → ℝ → ℝ`,
and `lam : Fin m → ℝ` are the dual multipliers (Lagrange multipliers). -/
noncomputable def lagrangian {m : ℕ} (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (lam : Fin m → ℝ) (x : ℝ) : ℝ :=
  f x + ∑ i, lam i * g i x

/-! ### Lemma 1: zero multipliers reduce to objective -/

/-- **Zero multipliers.**
When all Lagrange multipliers are zero, the Lagrangian equals the
objective function. The penalty terms all vanish because `0 * g_i(x) = 0`.

Proof: rewrite the sum using `Finset.sum_eq_zero` after applying
`zero_mul` to each term. -/
@[stat_lemma]
theorem lagrangian_at_zero_multipliers {m : ℕ} (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (x : ℝ) :
    lagrangian f g (fun _ => 0) x = f x := by
  unfold lagrangian
  simp [zero_mul]

/-! ### Lemma 2: Lagrangian <= objective at feasible points -/

/-- **Lagrangian at feasible point with nonneg multipliers.**
For a feasible point x (all g_i(x) <= 0) and nonneg multipliers
(all lambda_i >= 0), each penalty term satisfies

    lambda_i * g_i(x) <= 0

because it is the product of a nonneg and a nonpos number. Hence the
sum of penalties is nonpositive, and

    L(x, lambda) = f(x) + sum_i lambda_i * g_i(x) <= f(x).

Uses `mul_nonpos_of_nonneg_of_nonpos` for each term, `Finset.sum_nonpos`
for the sum, and `add_le_of_nonpos_right` for the final inequality. -/
@[stat_lemma]
theorem lagrangian_le_objective_at_feasible {m : ℕ}
    (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (lam : Fin m → ℝ) (x : ℝ)
    (h_feas : ∀ i : Fin m, g i x ≤ 0)
    (h_lam : ∀ i : Fin m, 0 ≤ lam i) :
    lagrangian f g lam x ≤ f x := by
  unfold lagrangian
  apply add_le_of_nonpos_right
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos (h_lam i) (h_feas i)

/-! ### Lemma 3: Weak duality -/

/-- **Weak duality.**
For any feasible point x (all g_i(x) <= 0), any nonneg multipliers
(all lambda_i >= 0), and any lower bound d on the Lagrangian
(d <= L(x, lambda) for all y), we have

    d <= f(x).

The proof chains the lower bound hypothesis at y = x with
`lagrangian_le_objective_at_feasible`. -/
@[stat_lemma]
theorem weak_duality {m : ℕ}
    (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (lam : Fin m → ℝ) (x : ℝ) (d : ℝ)
    (h_feas : ∀ i : Fin m, g i x ≤ 0)
    (h_lam : ∀ i : Fin m, 0 ≤ lam i)
    (h_lb : ∀ y : ℝ, d ≤ lagrangian f g lam y) :
    d ≤ f x :=
  (h_lb x).trans (lagrangian_le_objective_at_feasible f g lam x h_feas h_lam)

/-! ### Lemma 4: Tight constraint does not change Lagrangian value -/

/-- **Complementary-slackness style: tight constraint.**
If the i-th constraint is tight at x (g_i(x) = 0), then changing the
i-th multiplier from `lam i` to any other value `lam' i` (while keeping
all other multipliers fixed) does not change the Lagrangian value at x.

Formally, for functions `lam lam' : Fin m → ℝ` that agree on all j != i,
if g_i(x) = 0 then `lagrangian f g lam x = lagrangian f g lam' x`. -/
@[stat_lemma]
theorem lagrangian_mono_multiplier {m : ℕ}
    (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (lam lam' : Fin m → ℝ) (x : ℝ) (i : Fin m)
    (h_tight : g i x = 0)
    (h_other : ∀ j : Fin m, j ≠ i → lam j = lam' j) :
    lagrangian f g lam x = lagrangian f g lam' x := by
  unfold lagrangian
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : j = i
  · subst hij
    simp [h_tight]
  · rw [h_other j hij]

/-! ### Lemma 5: Duality gap is nonneg -/

/-- **Nonneg duality gap.**
The duality gap `f(x) - d(lambda)` is nonneg for any feasible x,
nonneg multipliers, and lower bound d on the Lagrangian.

This is a direct restatement of weak duality as a nonnegativity claim
on the gap `f(x) - d`. -/
@[stat_lemma]
theorem duality_gap_nonneg {m : ℕ}
    (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (lam : Fin m → ℝ) (x : ℝ) (d : ℝ)
    (h_feas : ∀ i : Fin m, g i x ≤ 0)
    (h_lam : ∀ i : Fin m, 0 ≤ lam i)
    (h_lb : ∀ y : ℝ, d ≤ lagrangian f g lam y) :
    0 ≤ f x - d :=
  sub_nonneg.mpr (weak_duality f g lam x d h_feas h_lam h_lb)

end Pythia.Optimization
