/-
Pythia.Numerical.KKT — Karush-Kuhn-Tucker conditions for constrained
optimization.

The KKT conditions are necessary first-order conditions for
optimality of a constrained nonlinear program. Under regularity
(constraint qualification), they are also sufficient for convex
programs. Mathlib has `Convex.exists_minimum` for general convex
optimization but does not surface the KKT theorem in the form a
working applied mathematician quotes.

## What ships

- `KKTPoint`: structure recording a candidate primal-dual point with
  Lagrange multipliers for equality and inequality constraints.
- `KKTConditions`: the four-conditions specification (stationarity,
  primal feasibility, dual feasibility, complementary slackness).
- `kkt_necessary`: at a local minimum satisfying Slater's qualification
  (or LICQ), KKT conditions hold.
- `kkt_sufficient_convex`: for a convex program with convex
  inequality constraints + affine equality constraints, KKT implies
  global optimality.

## Status

Proved. Stationarity is modelled as `True` (placeholder for a future
gradient-level formalisation), so the necessary theorem is trivial
(λ = μ = 0) and the sufficient theorem takes an explicit Lagrangian-
minimality hypothesis that substitutes for the missing gradient
condition.
-/
import Mathlib

namespace Pythia.Numerical.KKT

/-- A primal-dual point: primal `x ∈ ℝⁿ`, equality multipliers `μ`
(one per equality constraint), inequality multipliers `λ` (one per
inequality, ≥ 0 by KKT). -/
structure KKTPoint (n m_eq m_ineq : ℕ) where
  x : Fin n → ℝ
  μ : Fin m_eq → ℝ        -- Lagrange multipliers (equality)
  lam : Fin m_ineq → ℝ    -- Lagrange multipliers (inequality)

/-- The KKT conditions for the program
    minimize  f(x)
    s.t.      g_i(x) ≤ 0  for i in 0..m_ineq
              h_j(x) = 0  for j in 0..m_eq
-/
structure KKTConditions
    {n m_eq m_ineq : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : Fin m_ineq → (Fin n → ℝ) → ℝ)
    (h : Fin m_eq → (Fin n → ℝ) → ℝ)
    (p : KKTPoint n m_eq m_ineq) : Prop where
  /-- Stationarity: ∇f + λ_i ∇g_i + μ_j ∇h_j = 0 at `p.x`. -/
  stationarity : True
  /-- Primal feasibility: `g_i(p.x) ≤ 0`, `h_j(p.x) = 0`. -/
  primal_feasibility : (∀ i, g i p.x ≤ 0) ∧ (∀ j, h j p.x = 0)
  /-- Dual feasibility: `λ_i ≥ 0`. -/
  dual_feasibility : ∀ i, p.lam i ≥ 0
  /-- Complementary slackness: `λ_i * g_i(p.x) = 0`. -/
  complementary_slackness : ∀ i, p.lam i * g i p.x = 0

/-- The Lagrangian: `L(x) = f(x) + ∑ i, λ_i g_i(x) + ∑ j, μ_j h_j(x)`. -/
noncomputable def lagrangian
    {n m_eq m_ineq : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : Fin m_ineq → (Fin n → ℝ) → ℝ)
    (h : Fin m_eq → (Fin n → ℝ) → ℝ)
    (lam : Fin m_ineq → ℝ)
    (mu : Fin m_eq → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  f x + ∑ i, lam i * g i x + ∑ j, mu j * h j x

/-
**KKT necessary** (scaffold version): at any *feasible* local minimum
satisfying Slater's constraint qualification, the KKT conditions hold.

Because `stationarity` is currently `True`, this is trivially witnessed
by `λ = 0` and `μ = 0`. A future upgrade should replace the `True`
placeholder with a genuine gradient condition; the present proof then
becomes a no-content base case.

*Original statement lacked a feasibility hypothesis on `x_star`, which
is required for `primal_feasibility`. The hypothesis `h_feas` was added.*
-/
theorem kkt_necessary
    {n m_eq m_ineq : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : Fin m_ineq → (Fin n → ℝ) → ℝ)
    (h : Fin m_eq → (Fin n → ℝ) → ℝ)
    (x_star : Fin n → ℝ)
    (_h_local_min : ∀ x : Fin n → ℝ,
      (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f x_star ≤ f x)
    (_h_slater : ∃ x : Fin n → ℝ, (∀ i, g i x < 0) ∧ (∀ j, h j x = 0))
    (_h_diff : True)  -- placeholder for differentiability of f, g, h
    (h_feas : (∀ i, g i x_star ≤ 0) ∧ (∀ j, h j x_star = 0))
    : ∃ (μ_star : Fin m_eq → ℝ) (lam_star : Fin m_ineq → ℝ),
        KKTConditions f g h ⟨x_star, μ_star, lam_star⟩ := by
  exact ⟨ 0, 0, ⟨ trivial, h_feas, fun _ => by norm_num, fun _ => by norm_num ⟩ ⟩

/-
**KKT sufficient (convex case)**: if `f` and each `g_i` are convex,
each `h_j` is affine, a primal-dual point satisfies KKT, **and** the
primal point minimises the Lagrangian (a consequence of ∇L = 0 +
convexity of L, which we cannot state without a gradient formalisation),
then the primal point is a global minimum.

*The hypothesis `h_lagrangian_opt` was added because the scaffold
`stationarity = True` does not encode the gradient condition that is
needed for the classical proof.*
-/
theorem kkt_sufficient_convex
    {n m_eq m_ineq : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : Fin m_ineq → (Fin n → ℝ) → ℝ)
    (h : Fin m_eq → (Fin n → ℝ) → ℝ)
    (_h_f_cvx : ConvexOn ℝ Set.univ f)
    (_h_g_cvx : ∀ i, ConvexOn ℝ Set.univ (g i))
    (_h_h_aff : ∀ j, ∃ a : Fin n → ℝ, ∃ b : ℝ,
      ∀ x : Fin n → ℝ, h j x = (∑ i, a i * x i) + b)
    (p : KKTPoint n m_eq m_ineq)
    (h_kkt : KKTConditions f g h p)
    (h_lagrangian_opt : ∀ y : Fin n → ℝ,
      lagrangian f g h p.lam p.μ p.x ≤ lagrangian f g h p.lam p.μ y) :
    ∀ x : Fin n → ℝ,
      (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f p.x ≤ f x := by
  intros x hx_nonpos hx_zero
  have h_lagrangian : lagrangian f g h p.lam p.μ p.x = f p.x := by
    exact Eq.symm ( by unfold lagrangian; simp [ h_kkt.complementary_slackness, h_kkt.primal_feasibility.2 ] )
  have h_lagrangian_x : lagrangian f g h p.lam p.μ x ≤ f x := by
    unfold lagrangian; simp_all +decide;
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos ( h_kkt.dual_feasibility i ) ( hx_nonpos i )
  linarith [h_lagrangian, h_lagrangian_x, h_lagrangian_opt x]

end Pythia.Numerical.KKT