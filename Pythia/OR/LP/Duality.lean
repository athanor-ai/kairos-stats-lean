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

/-- **Strong LP duality.** If the primal has a feasible solution and
the dual has a feasible solution, then the optimal primal value equals
the optimal dual value.

Stated as: there exist optimal x* and y* achieving cᵀx* = bᵀy*. -/
theorem strong_duality (P : LP n m)
    (hpf : ∃ x, P.primalFeasible x)
    (hdf : ∃ y, P.dualFeasible y) :
    ∃ x y, P.primalFeasible x ∧ P.dualFeasible y ∧
      P.primalObj x = P.dualObj y := by
  sorry

end Pythia.OR.LP
