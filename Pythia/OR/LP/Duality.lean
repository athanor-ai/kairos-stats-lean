/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Linear Programming Duality

Weak and strong duality for finite-dimensional linear programs in
standard form. General applied mathematics.

## Primal (standard form)

  minimize    c ᵀ x
  subject to  A x ≥ b,  x ≥ 0

## Dual

  maximize    b ᵀ y
  subject to  A ᵀ y ≤ c,  y ≥ 0

## Theorems

* `weak_duality`: for any primal-feasible x and dual-feasible y,
  b ᵀ y ≤ c ᵀ x. The dual objective is always a lower bound on
  the primal objective.

* `strong_duality`: if both the primal and dual have feasible solutions,
  then their optimal values are equal. (Requires a constraint
  qualification — here we assume both are feasible, which suffices
  for the finite-dimensional LP case.)

## References

* Bertsimas & Tsitsiklis, "Introduction to Linear Optimization" (1997), Ch. 4.
* Mathlib has no LP duality as of v4.28 — this is Pythia-original.
-/
import Mathlib

open scoped Matrix BigOperators

noncomputable section

namespace Pythia.OR.LP

variable {n m : ℕ}

/-- A linear program in standard form: minimize cᵀx subject to Ax ≥ b, x ≥ 0. -/
structure LP (n m : ℕ) where
  c : Fin n → ℝ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ

/-- Primal feasibility: Ax ≥ b and x ≥ 0. -/
def LP.primalFeasible (P : LP n m) (x : Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, P.A i j * x j ≥ P.b i) ∧ (∀ j, 0 ≤ x j)

/-- Dual feasibility: Aᵀy ≤ c and y ≥ 0. -/
def LP.dualFeasible (P : LP n m) (y : Fin m → ℝ) : Prop :=
  (∀ j, ∑ i, P.A i j * y i ≤ P.c j) ∧ (∀ i, 0 ≤ y i)

/-- Primal objective: cᵀx. -/
def LP.primalObj (P : LP n m) (x : Fin n → ℝ) : ℝ :=
  ∑ j, P.c j * x j

/-- Dual objective: bᵀy. -/
def LP.dualObj (P : LP n m) (y : Fin m → ℝ) : ℝ :=
  ∑ i, P.b i * y i

/-- **Weak LP duality.** For any primal-feasible x and dual-feasible y,
the dual objective is at most the primal objective: bᵀy ≤ cᵀx.

Proof idea: bᵀy ≤ (Ax)ᵀy = xᵀ(Aᵀy) ≤ xᵀc = cᵀx, using
primal feasibility (Ax ≥ b, x ≥ 0) and dual feasibility (Aᵀy ≤ c, y ≥ 0). -/
theorem weak_duality (P : LP n m) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : P.primalFeasible x) (hy : P.dualFeasible y) :
    P.dualObj y ≤ P.primalObj x := by
  obtain ⟨hAx, hx0⟩ := hx
  obtain ⟨hAty, hy0⟩ := hy
  simp only [LP.dualObj, LP.primalObj]
  -- Step 1: b i * y i ≤ (∑ j, A i j * x j) * y i  (from Ax ≥ b and y ≥ 0)
  -- Step 2: swap the double sum
  -- Step 3: (∑ i, A i j * y i) * x j ≤ c j * x j  (from Aᵀy ≤ c and x ≥ 0)
  calc ∑ i, P.b i * y i
      ≤ ∑ i, (∑ j, P.A i j * x j) * y i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hAx i) (hy0 i)
    _ = ∑ j, (∑ i, P.A i j * y i) * x j := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        congr 1; ext j
        congr 1; ext i
        ring
    _ ≤ ∑ j, P.c j * x j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hAty j) (hx0 j)

-- -------------------------------------------------------------------------
-- Auxiliary lemmas for strong duality
-- -------------------------------------------------------------------------

/-- **Gap decomposition identity.**
The duality gap cᵀx − bᵀy decomposes into a sum of non-negative
complementary-slackness products:

  cᵀx − bᵀy
    = ∑ⱼ (cⱼ − (Aᵀy)ⱼ) xⱼ   (dual-slack × primal-var)
    + ∑ᵢ yᵢ ((Ax)ᵢ − bᵢ)     (dual-var × primal-slack)

Both sums are non-negative when x and y are feasible.  The identity
itself is purely algebraic and holds for any x, y. -/
private lemma gap_decomp (P : LP n m) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    ∑ j : Fin n, (P.c j - ∑ i, P.A i j * y i) * x j +
    ∑ i : Fin m, y i * (∑ j, P.A i j * x j - P.b i) =
    P.primalObj x - P.dualObj y := by
  simp only [LP.primalObj, LP.dualObj]
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  -- Rewrite the cross-term ∑ⱼ (∑ᵢ Aᵢⱼ yᵢ) xⱼ = ∑ᵢ yᵢ ∑ⱼ Aᵢⱼ xⱼ
  have cross : ∑ j : Fin n, (∑ i : Fin m, P.A i j * y i) * x j =
               ∑ i : Fin m, y i * ∑ j : Fin n, P.A i j * x j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  linarith [cross,
    show ∑ i : Fin m, y i * P.b i = ∑ i : Fin m, P.b i * y i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)]

/-- **Complementary slackness.**
If x is primal-feasible, y is dual-feasible, and cᵀx = bᵀy (zero duality gap),
then every complementary-slackness product is zero:
- (cⱼ − (Aᵀy)ⱼ) · xⱼ = 0  for all j  (either dual constraint is tight or xⱼ = 0)
- yᵢ · ((Ax)ᵢ − bᵢ) = 0    for all i  (either yᵢ = 0 or primal constraint is tight)

This is a fully algebraic consequence of `gap_decomp` and non-negativity of each term. -/
lemma complementary_slackness (P : LP n m) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : P.primalFeasible x) (hy : P.dualFeasible y)
    (hgap : P.primalObj x = P.dualObj y) :
    (∀ j, (P.c j - ∑ i, P.A i j * y i) * x j = 0) ∧
    (∀ i, y i * (∑ j, P.A i j * x j - P.b i) = 0) := by
  obtain ⟨hAx, hx0⟩ := hx
  obtain ⟨hAty, hy0⟩ := hy
  -- Each complementary product is non-negative
  have h1 : ∀ j : Fin n, 0 ≤ (P.c j - ∑ i, P.A i j * y i) * x j :=
    fun j => mul_nonneg (by linarith [hAty j]) (hx0 j)
  have h2 : ∀ i : Fin m, 0 ≤ y i * (∑ j, P.A i j * x j - P.b i) :=
    fun i => mul_nonneg (hy0 i) (by linarith [hAx i])
  -- The two sums are non-negative individually
  have hS1 : 0 ≤ ∑ j : Fin n, (P.c j - ∑ i, P.A i j * y i) * x j :=
    Finset.sum_nonneg (fun j _ => h1 j)
  have hS2 : 0 ≤ ∑ i : Fin m, y i * (∑ j, P.A i j * x j - P.b i) :=
    Finset.sum_nonneg (fun i _ => h2 i)
  -- Their total equals the duality gap, which is zero
  have hgap0 : P.primalObj x - P.dualObj y = 0 := sub_eq_zero.mpr hgap
  have hS1z : ∑ j : Fin n, (P.c j - ∑ i, P.A i j * y i) * x j = 0 :=
    le_antisymm (by linarith [gap_decomp P x y]) hS1
  have hS2z : ∑ i : Fin m, y i * (∑ j, P.A i j * x j - P.b i) = 0 :=
    le_antisymm (by linarith [gap_decomp P x y]) hS2
  -- A non-negative sum is zero iff every term is zero
  exact ⟨fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h1 j)).mp hS1z j
                    (Finset.mem_univ j),
         fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h2 i)).mp hS2z i
                    (Finset.mem_univ i)⟩

-- -------------------------------------------------------------------------
-- The two hard steps: existence of optimal solutions (require Farkas' lemma)
-- -------------------------------------------------------------------------

/-- **Existence of a primal minimizer.**
When the primal LP is feasible and dual feasibility gives a lower bound on cᵀx,
a primal minimizer exists.  The argument runs:
1. Dual feasibility + weak duality ⟹  inf{cᵀx : x primal-feasible} ≥ bᵀy₀ > −∞.
2. The feasible set is a closed (Aᵢ-halfspace ∩ non-negative orthant) polyhedron.
3. By the LP attainment theorem (a consequence of Farkas' lemma / the simplex
   algorithm's finiteness), the infimum of a linear objective over a non-empty
   polyhedron that is bounded below is attained at a vertex.

**TODO:** Formalize in Lean once Mathlib has Farkas' lemma or LP attainment.
See Bertsimas & Tsitsiklis (1997) Ch. 4, Theorem 4.4. -/
private lemma exists_primal_optimal (P : LP n m)
    (hpf : ∃ x, P.primalFeasible x)
    (hdf : ∃ y, P.dualFeasible y) :
    ∃ xopt, P.primalFeasible xopt ∧
            ∀ x, P.primalFeasible x → P.primalObj xopt ≤ P.primalObj x := by
  sorry
  -- Proof sketch:
  -- obtain ⟨y₀, hy₀⟩ := hdf
  -- Lower bound: ∀ x primal-feas, P.primalObj x ≥ P.dualObj y₀ (weak duality)
  -- Attainment: by LP finiteness / compactness of level sets in standard-form LP

/-- **Existence of a complementary-slack dual optimizer.**
Given a primal minimizer xopt, there exists a dual-feasible yopt with
bᵀyopt = cᵀxopt (no duality gap).
This follows from the KKT (Karush-Kuhn-Tucker) optimality conditions for LP:
- Primal stationarity: ∃ y ≥ 0 with Aᵀy ≤ c.
- Dual complementary slackness: (cⱼ − (Aᵀy)ⱼ) xoptⱼ = 0 for all j.
- Primal complementary slackness: yᵢ ((Axopt)ᵢ − bᵢ) = 0 for all i.
These conditions together force bᵀy = cᵀxopt.

**TODO:** Formalize using KKT / Farkas' lemma once available in Mathlib. -/
private lemma exists_dual_from_primal_opt (P : LP n m)
    (hdf : ∃ y, P.dualFeasible y)
    (xopt : Fin n → ℝ) (hxopt : P.primalFeasible xopt)
    (hopt : ∀ x, P.primalFeasible x → P.primalObj xopt ≤ P.primalObj x) :
    ∃ yopt, P.dualFeasible yopt ∧ P.primalObj xopt = P.dualObj yopt := by
  sorry
  -- Proof sketch:
  -- Use the Farkas alternative applied to the system
  --   { Ax ≥ b, x ≥ 0, cᵀx < cᵀxopt }
  -- which is infeasible (by optimality of xopt).
  -- Farkas' lemma then produces y ≥ 0 with Aᵀy ≤ c and bᵀy = cᵀxopt.

-- -------------------------------------------------------------------------
-- Main theorem
-- -------------------------------------------------------------------------

/-- **Strong LP duality.** If the primal has a feasible solution and
the dual has a feasible solution, then the optimal primal value equals
the optimal dual value.

Stated as: there exist optimal x* and y* achieving cᵀx* = bᵀy*.

**Proof outline:**
1. `exists_primal_optimal` — produces a primal minimizer xopt (sorry: needs Farkas).
2. `exists_dual_from_primal_opt` — produces a dual maximizer yopt with gap = 0
   (sorry: needs KKT / Farkas).
3. The conclusion follows directly.

The two sorry'd steps are the only remaining gaps; everything else
(weak duality, gap decomposition, complementary slackness) is fully proved. -/
theorem strong_duality (P : LP n m)
    (hpf : ∃ x, P.primalFeasible x)
    (hdf : ∃ y, P.dualFeasible y) :
    ∃ x y, P.primalFeasible x ∧ P.dualFeasible y ∧
      P.primalObj x = P.dualObj y := by
  -- Step 1: obtain a primal minimizer
  obtain ⟨xopt, hxopt_feas, hxopt_opt⟩ := exists_primal_optimal P hpf hdf
  -- Step 2: obtain a dual solution matching the primal optimum
  obtain ⟨yopt, hyopt_feas, hgap⟩ :=
    exists_dual_from_primal_opt P hdf xopt hxopt_feas hxopt_opt
  -- Step 3: the pair (xopt, yopt) witnesses strong duality
  exact ⟨xopt, yopt, hxopt_feas, hyopt_feas, hgap⟩

end Pythia.OR.LP
