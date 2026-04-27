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
is non-positive in a neighborhood of 0.

Closed 2026-04-27 (research): scalar IVT-and-monotonicity proof.
The Lie-derivative-≤-0 hypothesis gives V ∘ y antitone on Ici 0
(via `antitoneOn_of_deriv_nonpos`); combined with the boundary
minimum `m := min(V(-ε), V(ε)) > 0` and continuity-at-0 + IVT to
locate a boundary crossing, the standard contradiction closes
in ~50 lines of Mathlib API. Mathlib v4.28.0 had every prerequisite
(`intermediate_value_Icc`, `antitoneOn_of_deriv_nonpos`,
`HasDerivAt.comp`, `Metric.continuousAt_iff`); no structural gap
after all. -/
theorem lyapunov_stable
    (f : ℝ → ℝ) (_h_zero : f 0 = 0)
    (V : ℝ → ℝ) (h_V_zero : V 0 = 0)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_lie : ∀ y : ℝ, deriv V y * f y ≤ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) →
      |y 0| < δ →
      ∀ t ≥ (0 : ℝ), |y t| < ε := by
  intro ε hε
  -- Step 1: positive minimum on the boundary {-ε, ε}.
  have hε_neg_ne : (-ε : ℝ) ≠ 0 := by linarith
  have hε_pos_ne : (ε : ℝ) ≠ 0 := by linarith
  set m := min (V (-ε)) (V ε) with _hm_def
  have hm_pos : 0 < m :=
    lt_min (h_V_pos (-ε) hε_neg_ne) (h_V_pos ε hε_pos_ne)
  -- Step 2: continuity at 0 + V(0) = 0 ⇒ ∃ δ₁ > 0, |y| < δ₁ ⇒ V y < m.
  have h_V_cont0 : ContinuousAt V 0 := (h_V_diff 0).continuousAt
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ y : ℝ, |y| < δ₁ → V y < m := by
    rcases Metric.continuousAt_iff.mp h_V_cont0 m hm_pos with ⟨δ₁, hδ₁_pos, hd⟩
    refine ⟨δ₁, hδ₁_pos, fun y hy => ?_⟩
    have hdy : dist y 0 < δ₁ := by simpa [Real.dist_eq] using hy
    have habs : |V y - V 0| < m := by simpa [Real.dist_eq] using hd hdy
    rw [h_V_zero, sub_zero] at habs
    linarith [(abs_lt.mp habs).2]
  refine ⟨min δ₁ ε, lt_min hδ₁_pos hε,
           fun y hy_ode hy_init t ht => ?_⟩
  -- Step 3: contradiction.
  by_contra h_not
  push_neg at h_not
  -- y is continuous (each HasDerivAt is continuous at its point).
  have hy_cont : Continuous y :=
    continuous_iff_continuousAt.mpr fun s => (hy_ode s).differentiableAt.continuousAt
  have habs_cont : Continuous (fun s => |y s|) := hy_cont.abs
  -- |y 0| < ε ≤ |y t|, so by IVT there is some s ∈ [0, t] with |y s| = ε.
  have hy0_lt_ε : |y 0| < ε := lt_of_lt_of_le hy_init (min_le_right _ _)
  obtain ⟨s, hs_mem, hs_eq⟩ : ∃ s ∈ Set.Icc (0 : ℝ) t, |y s| = ε := by
    have hcont : ContinuousOn (fun s => |y s|) (Set.Icc 0 t) :=
      habs_cont.continuousOn
    rcases intermediate_value_Icc ht hcont ⟨hy0_lt_ε.le, h_not⟩
      with ⟨s, hs1, hs2⟩
    exact ⟨s, hs1, hs2⟩
  -- At s, V(y s) ≥ m (since |y s| = ε means y s = ε or y s = -ε).
  have hV_ys_ge_m : m ≤ V (y s) := by
    rcases abs_eq hε.le |>.mp hs_eq with hpos | hneg
    · rw [hpos]; exact min_le_right _ _
    · rw [hneg]; exact min_le_left _ _
  -- Antitonicity of V ∘ y on [0, ∞) via Lie-derivative ≤ 0.
  have h_V_y_diff : ∀ u : ℝ, HasDerivAt (V ∘ y) (deriv V (y u) * f (y u)) u := by
    intro u
    have hV_at : HasDerivAt V (deriv V (y u)) (y u) := (h_V_diff (y u)).hasDerivAt
    exact hV_at.comp u (hy_ode u)
  have h_antitone : AntitoneOn (V ∘ y) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun u _ => ((h_V_y_diff u).continuousAt).continuousWithinAt
    · exact fun u _ => ((h_V_y_diff u).differentiableAt).differentiableWithinAt
    · intro u _; rw [(h_V_y_diff u).deriv]; exact h_lie (y u)
  -- V(y s) ≤ V(y 0).
  have hVys_le_Vy0 : V (y s) ≤ V (y 0) :=
    h_antitone Set.self_mem_Ici hs_mem.1 hs_mem.1
  -- V(y 0) < m since |y 0| < δ₁.
  have hy0_abs_lt_δ₁ : |y 0| < δ₁ := lt_of_lt_of_le hy_init (min_le_left _ _)
  have hVy0_lt_m : V (y 0) < m := hδ₁ (y 0) hy0_abs_lt_δ₁
  -- Contradiction: m ≤ V(y s) ≤ V(y 0) < m.
  linarith

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
