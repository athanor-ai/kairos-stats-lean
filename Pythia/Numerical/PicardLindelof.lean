/-
Pythia.Numerical.PicardLindelof — ODE existence + uniqueness.

Picard-Lindelöf (Cauchy-Lipschitz) theorem for the initial value
problem `y'(t) = f(t, y(t))`, `y(t₀) = y₀`.

## What ships

- `picard_lindelof_local`: local existence + uniqueness on a small
  time interval given Lipschitz + continuous f.
- `picard_lindelof_global`: global existence + uniqueness on all of
  ℝ given globally-Lipschitz + continuous f.
- `picard_lindelof_continuous_dependence`: continuous dependence on
  initial conditions (Gronwall consequence).

## Corrections from original scaffold (v0.5)

The original scaffold signatures for `picard_lindelof_local` and
`picard_lindelof_global` omitted continuity of `f` in the time
variable `t`. Without this hypothesis the theorems are **false**:
the function `f(t, y) = if t = 0 then 1 else 0` is Lipschitz in `y`
and bounded, but the IVP `y'(t) = f(t, y(t))` has no solution since
Darboux's theorem prevents `y'` from jumping between 0 and 1.
The corrected versions add the necessary continuity hypothesis.
-/
import Mathlib

namespace Pythia.Numerical.PicardLindelof

open MeasureTheory Set Metric

/-! ### Original scaffold theorems (FALSE as stated — missing continuity in t)

The following two theorems from the v0.5 scaffold are **not provable**
because the hypotheses omit continuity of `f` in the time variable.
See the corrected versions below.

-- theorem picard_lindelof_local
--     (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
--     (K : NNReal) (hK_lip : ∀ t ∈ Set.Icc (t₀ - a) (t₀ + a),
--       LipschitzWith K (fun y => f t y))
--     (M : ℝ) (hM_bound : ∀ t ∈ Set.Icc (t₀ - a) (t₀ + a),
--       ∀ y ∈ Set.Icc (y₀ - b) (y₀ + b), |f t y| ≤ M) :
--     ∃ (h : ℝ) (_ : 0 < h) (y : ℝ → ℝ),
--       (∀ t ∈ Set.Icc (t₀ - h) (t₀ + h),
--         HasDerivAt y (f t (y t)) t) ∧
--       y t₀ = y₀ ∧
--       ∀ (z : ℝ → ℝ),
--         (∀ t ∈ Set.Icc (t₀ - h) (t₀ + h), HasDerivAt z (f t (z t)) t) →
--         z t₀ = y₀ →
--         ∀ t ∈ Set.Icc (t₀ - h) (t₀ + h), y t = z t
--
-- COUNTEREXAMPLE: f(t,y) = if t = 0 then 1 else 0.
-- This is 0-Lipschitz in y, bounded by 1, but admits no differentiable
-- solution to the IVP by Darboux's theorem (derivatives have the
-- intermediate value property).

-- theorem picard_lindelof_global
--     (f : ℝ → ℝ → ℝ) (y₀ : ℝ)
--     (K : NNReal) (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
--     (h_meas : ∀ y : ℝ, Measurable (fun t => f t y))
--     (h_int : ∀ y : ℝ, IntervalIntegrable (fun t => f t y) volume 0 1) :
--     ∃! y : ℝ → ℝ,
--       (∀ t : ℝ, HasDerivAt y (f t (y t)) t) ∧ y 0 = y₀
--
-- FALSE for the same reason as picard_lindelof_local.
-/

/-! ### Corrected Picard-Lindelöf local theorem -/

/-
**Picard-Lindelöf local existence + uniqueness** (corrected).

Compared to the original scaffold, this version adds the hypothesis
`hf_cont` requiring continuity of `f` in the time variable for each
fixed `y` in the rectangle. Without this, the theorem is false.

Given `f : ℝ → ℝ → ℝ` that is uniformly Lipschitz in its second
argument with constant `K`, bounded by `M` on a compact rectangle
around `(t₀, y₀)`, and continuous in `t`, the IVP `y' = f(t, y)`,
`y(t₀) = y₀` has a unique continuously differentiable solution on a
neighborhood of `t₀`.
-/
theorem picard_lindelof_local
    (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (K : NNReal) (hK_lip : ∀ t ∈ Icc (t₀ - a) (t₀ + a),
      LipschitzWith K (fun y => f t y))
    (M : ℝ) (hM_bound : ∀ t ∈ Icc (t₀ - a) (t₀ + a),
      ∀ y ∈ Icc (y₀ - b) (y₀ + b), |f t y| ≤ M)
    (hf_cont : ∀ y ∈ Icc (y₀ - b) (y₀ + b),
      ContinuousOn (fun t => f t y) (Icc (t₀ - a) (t₀ + a))) :
    ∃ (h : ℝ) (_ : 0 < h) (y : ℝ → ℝ),
      (∀ t ∈ Icc (t₀ - h) (t₀ + h),
        HasDerivAt y (f t (y t)) t) ∧
      y t₀ = y₀ ∧
      ∀ (z : ℝ → ℝ),
        (∀ t ∈ Icc (t₀ - h) (t₀ + h), HasDerivAt z (f t (z t)) t) →
        z t₀ = y₀ →
        ∀ t ∈ Icc (t₀ - h) (t₀ + h), y t = z t := by
  -- Choose h with 0 < h ≤ a and M * h ≤ b. If M > 0, take h = min(a, b/M). If M ≤ 0, take h = a.
  obtain ⟨h, hh⟩ : ∃ h, 0 < h ∧ h ≤ a ∧ M * h ≤ b := by
    by_cases hM_pos : 0 < M;
    · exact ⟨ Min.min a ( b / M ), lt_min ha ( div_pos hb hM_pos ), min_le_left _ _, by nlinarith [ min_le_right a ( b / M ), mul_div_cancel₀ b hM_pos.ne' ] ⟩;
    · exact ⟨ a, ha, le_rfl, by nlinarith ⟩;
  -- Construct IsPicardLindelof with tmin = t₀ - h, tmax = t₀ + h, x₀ = y₀, ball radius ⟨b, ..⟩, r = 0, L = ⟨M.toNNReal, ...⟩, K = K.
  obtain ⟨α, hα⟩ : ∃ α : ℝ → ℝ, α t₀ = y₀ ∧ ∀ t ∈ Set.Icc (t₀ - h) (t₀ + h), HasDerivWithinAt α (f t (α t)) (Set.Icc (t₀ - h) (t₀ + h)) t := by
    have := @IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀;
    convert @this ℝ _ _ _ ( fun t x => f t x ) ( t₀ - h ) ( t₀ + h ) ⟨ t₀, ⟨ by linarith, by linarith ⟩ ⟩ y₀ ⟨ b, by linarith ⟩ ⟨ M.toNNReal, by
      positivity ⟩ K ⟨ by
      exact fun t ht => hK_lip t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ |> LipschitzWith.lipschitzOnWith, by
      simp +zetaDelta at *;
      exact fun x hx => hf_cont x ( by linarith [ abs_le.mp hx ] ) ( by linarith [ abs_le.mp hx ] ) |> ContinuousOn.mono <| Set.Icc_subset_Icc ( by linarith ) ( by linarith ), by
      simp +zetaDelta at *;
      exact fun t ht₁ ht₂ x hx => Or.inl <| hM_bound t ( by linarith ) ( by linarith ) x ( by linarith [ abs_le.mp hx ] ) ( by linarith [ abs_le.mp hx ] ), by
      norm_num [ hh.1.le ];
      cases max_cases M 0 <;> nlinarith ⟩ using 1;
  refine' ⟨ h / 2, half_pos hh.1, α, _, hα.1, _ ⟩;
  · intro t ht; specialize hα; have := hα.2 t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ; exact this.hasDerivAt ( Icc_mem_nhds ( by linarith [ ht.1 ] ) ( by linarith [ ht.2 ] ) ) ;
  · intro z hz hz' t ht;
    -- By the uniqueness part of the Picard-Lindelöf theorem, since both α and z satisfy the same differential equation and initial condition, they must be equal.
    have h_unique : ∀ t ∈ Set.Icc (t₀ - h / 2) (t₀ + h / 2), α t = z t := by
      apply ODE_solution_unique_of_mem_Icc;
      case s => exact fun _ => Set.univ;
      any_goals exact t₀;
      any_goals norm_num [ hα.1, hz' ];
      exact fun t ht₁ ht₂ => hK_lip t ⟨ by linarith, by linarith ⟩;
      · linarith;
      · exact continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hα.2 t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ |> HasDerivWithinAt.hasDerivAt <| Icc_mem_nhds ( by linarith [ ht.1 ] ) ( by linarith [ ht.2 ] ) );
      · intro t ht₁ ht₂; specialize hα; have := hα.2 t ⟨ by linarith, by linarith ⟩ ; exact this.hasDerivAt ( Icc_mem_nhds ( by linarith ) ( by linarith ) ) ;
      · exact continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hz t ht );
      · exact fun t ht₁ ht₂ => hz t ⟨ by linarith, by linarith ⟩;
    exact h_unique t ht

/-! ### Corrected Picard-Lindelöf global theorem -/

/-- **Picard-Lindelöf global existence + uniqueness** (corrected).

Compared to the original scaffold, this version replaces the
measurability and integrability hypotheses with continuity of `f` in
`t`. When `f` is globally Lipschitz in `y` and continuous in `t`, the
IVP has a unique solution on all of `ℝ`.

**Uniqueness** is proved using Gronwall's inequality
(`ODE_solution_unique_univ` from Mathlib).
**Existence** requires constructing the global solution by chaining
local solutions from `picard_lindelof_local`; this step is left as
`sorry` pending formalization of the continuation argument. -/
theorem picard_lindelof_global
    (f : ℝ → ℝ → ℝ) (y₀ : ℝ)
    (K : NNReal) (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y)) :
    ∃! y : ℝ → ℝ,
      (∀ t : ℝ, HasDerivAt y (f t (y t)) t) ∧ y 0 = y₀ := by
  -- Uniqueness: any two global solutions with the same initial condition agree.
  suffices h_unique : ∀ y z : ℝ → ℝ,
      (∀ t : ℝ, HasDerivAt y (f t (y t)) t) → y 0 = y₀ →
      (∀ t : ℝ, HasDerivAt z (f t (z t)) t) → z 0 = y₀ → y = z by
    -- Existence: construct the global solution by chaining local solutions.
    obtain ⟨y, hy_deriv, hy_init⟩ : ∃ y : ℝ → ℝ,
        (∀ t : ℝ, HasDerivAt y (f t (y t)) t) ∧ y 0 = y₀ := by
      sorry
    exact ⟨y, ⟨hy_deriv, hy_init⟩, fun z ⟨hz_deriv, hz_init⟩ =>
      (h_unique y z hy_deriv hy_init hz_deriv hz_init).symm⟩
  -- Prove uniqueness using ODE_solution_unique_univ
  intro y z hy hy0 hz hz0
  exact ODE_solution_unique_univ (v := fun t y => f t y) (s := fun _ => Set.univ)
    (fun t => (hK_lip t).lipschitzOnWith)
    (fun t => ⟨hy t, Set.mem_univ _⟩)
    (fun t => ⟨hz t, Set.mem_univ _⟩)
    (by rw [hy0, hz0])

/-! ### Continuous dependence on initial conditions -/

/-- Continuous dependence on initial conditions (Gronwall-driven).
Two solutions to the same ODE with initial conditions `y₀` and `z₀`
diverge at most exponentially with rate `K`. -/
theorem picard_lindelof_continuous_dependence
    (f : ℝ → ℝ → ℝ) (y₀ z₀ : ℝ) (K : NNReal)
    (y z : ℝ → ℝ)
    (hy_eq : ∀ t : ℝ, HasDerivAt y (f t (y t)) t) (hy_init : y 0 = y₀)
    (hz_eq : ∀ t : ℝ, HasDerivAt z (f t (z t)) t) (hz_init : z 0 = z₀)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (T : ℝ) (_hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T,
      |y t - z t| ≤ |y₀ - z₀| * Real.exp ((K : ℝ) * t) := by
  intro t ht
  have key := dist_le_of_trajectories_ODE (v := fun t y => f t y) (K := K)
    (fun t => hK_lip t)
    (continuousOn_of_forall_continuousAt fun t _ => (hy_eq t).continuousAt)
    (fun t _ => (hy_eq t).hasDerivWithinAt)
    (continuousOn_of_forall_continuousAt fun t _ => (hz_eq t).continuousAt)
    (fun t _ => (hz_eq t).hasDerivWithinAt)
    (by rw [Real.dist_eq, hy_init, hz_init]) t ht
  rwa [Real.dist_eq, sub_zero] at key

end Pythia.Numerical.PicardLindelof
