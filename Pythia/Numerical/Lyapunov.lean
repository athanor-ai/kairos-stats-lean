/-
Pythia.Numerical.Lyapunov — Lyapunov stability for autonomous ODEs.

Lyapunov's direct method: stability of an equilibrium `y* = 0` of
the autonomous system `y'(t) = f(y(t))` follows from existence of a
positive-definite function `V : ℝ → ℝ` whose Lie derivative along
trajectories is non-positive (V decreases or stays flat along the
flow). Mathlib has nothing on Lyapunov stability; this module ships
the scaffolds.

## What ships

- `lyapunov_stable`: existence of a positive-definite `V` with
  non-positive Lie derivative implies Lyapunov stability of `y* = 0`.
- `lyapunov_asymptotic`: strict-decrease (Lie derivative strictly
  negative) implies asymptotic stability.
- `lasalle_invariance`: LaSalle's invariance principle: trajectories
  converge to the largest invariant subset of the zero-Lie-derivative
  set.

## Status

v0.5 scaffold. Theorem signatures defined; proofs scaffold-sorry
pending Aristotle queue items 31-33.
-/
import Mathlib

namespace Pythia.Numerical.Lyapunov

/-- Lyapunov stability: equilibrium `y* = 0` of `y' = f(y)` is stable
in the Lyapunov sense if there exists a continuously differentiable
positive-definite function `V` whose derivative along trajectories
is non-positive in a neighborhood of 0. -/
theorem lyapunov_stable
    (f : ℝ → ℝ) (h_zero : f 0 = 0)
    (V : ℝ → ℝ) (h_V_zero : V 0 = 0)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_lie : ∀ y : ℝ, deriv V y * f y ≤ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) →
      |y 0| < δ →
      ∀ t ≥ (0 : ℝ), |y t| < ε := by
  sorry  -- v0.5 scaffold; Aristotle queue item 31

/-- Asymptotic stability: when the Lie derivative is *strictly*
negative away from the equilibrium, trajectories not only stay near
zero but converge to it. -/
theorem lyapunov_asymptotic
    (f : ℝ → ℝ) (h_zero : f 0 = 0)
    (V : ℝ → ℝ) (h_V_zero : V 0 = 0)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_lie_strict : ∀ y : ℝ, y ≠ 0 → deriv V y * f y < 0) :
    ∃ δ > 0, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) →
      |y 0| < δ →
      Filter.Tendsto y Filter.atTop (nhds 0) := by
  sorry  -- v0.5 scaffold; Aristotle queue item 32

/-- LaSalle's invariance principle: when the Lie derivative is
non-positive but possibly zero on a set `E`, trajectories from a
compact level set converge to the LARGEST invariant set contained
in `E`. -/
theorem lasalle_invariance
    (f : ℝ → ℝ) (h_zero : f 0 = 0)
    (V : ℝ → ℝ) (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_lie : ∀ y : ℝ, deriv V y * f y ≤ 0)
    (c : ℝ) (h_c_pos : 0 < c)
    (Ω_c : Set ℝ) (h_Ω_c : Ω_c = {y | V y ≤ c})
    (E : Set ℝ) (h_E : E = {y | deriv V y * f y = 0})
    (M : Set ℝ) (h_M : M ⊆ E)
    (h_M_invariant : ∀ y₀ ∈ M, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) → y 0 = y₀ →
      ∀ t : ℝ, y t ∈ M) :
    ∀ y₀ ∈ Ω_c, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) → y 0 = y₀ →
      ∃ y_inf ∈ M, Filter.Tendsto y Filter.atTop (nhds y_inf) := by
  sorry  -- v0.5 scaffold; Aristotle queue item 33

end Pythia.Numerical.Lyapunov
