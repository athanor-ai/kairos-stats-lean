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

/-! ### Helper lemmas for global existence via chaining -/

/-- Step size for the chaining construction. Chosen so that `K * δ < 1`. -/
private noncomputable def globalStep (K : NNReal) : ℝ := 1 / ((K : ℝ) + 2)

/-
Single forward step: existence of a local solution on `[t₀, t₀ + globalStep K]`
via `IsPicardLindelof`.
-/
private lemma picard_one_step
    (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y))
    (t₀ v : ℝ) :
    ∃ y : ℝ → ℝ, y t₀ = v ∧
      ∀ t ∈ Icc t₀ (t₀ + globalStep K),
        HasDerivWithinAt y (f t (y t)) (Icc t₀ (t₀ + globalStep K)) t := by
  -- Let $M := \sup_{t \in [t₀, t₀ + globalStep K]} |f(t, v)|$. This is finite since $f(·, v)$ is continuous on a compact interval.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t ∈ Set.Icc t₀ (t₀ + globalStep K), |f t v| ≤ M := by
    exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) ( hf_cont v |> Continuous.continuousOn );
  -- Take $a := \langle M/2 + 1, by positivity \rangle : ℝ≥0$.
  set a : NNReal := ⟨M / 2 + 1, by
    linarith [ abs_le.mp ( hM t₀ ⟨ by norm_num, by linarith [ show 0 ≤ globalStep K from by exact div_nonneg zero_le_one ( by positivity ) ] ⟩ ) ]⟩
  generalize_proofs at *;
  -- Take $L := \langle M + K * (M / 2 + 1), by positivity \rangle : ℝ≥0$.
  set L : NNReal := ⟨M + K * (M / 2 + 1), by
    exact add_nonneg ( le_trans ( abs_nonneg _ ) ( hM t₀ ⟨ by norm_num, by linarith [ show 0 ≤ globalStep K from by exact div_nonneg zero_le_one ( by positivity ) ] ⟩ ) ) ( mul_nonneg ( NNReal.coe_nonneg _ ) ( by positivity ) )⟩
  generalize_proofs at *;
  have := @IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀;
  contrapose! this;
  refine' ⟨ ℝ, inferInstance, inferInstance, inferInstance, f, t₀, t₀ + globalStep K, ⟨ t₀, by norm_num; exact div_nonneg zero_le_one <| by positivity ⟩, v, a, L, K, _, _ ⟩ <;> norm_num;
  · constructor;
    · exact fun t ht => LipschitzWith.lipschitzOnWith ( hK_lip t );
    · exact fun x hx => Continuous.continuousOn ( hf_cont x );
    · intro t ht x hx; specialize hK_lip t; have := hK_lip.dist_le_mul x v; simp_all +decide [ dist_eq_norm ] ;
      simp +zetaDelta at *;
      exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp ( hM t ht.1 ht.2 ), abs_le.mp this, abs_le.mp hx, show ( K : ℝ ) ≥ 0 by positivity ], by nlinarith [ abs_le.mp ( hM t ht.1 ht.2 ), abs_le.mp this, abs_le.mp hx, show ( K : ℝ ) ≥ 0 by positivity ] ⟩;
    · simp +zetaDelta at *;
      rw [ max_eq_left ( by exact div_nonneg zero_le_one ( by positivity ) ) ];
      unfold globalStep; rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ NNReal.coe_nonneg K ] ;
  · exact fun α hα => by obtain ⟨ t, ht₁, ht₂ ⟩ := this α hα; exact ⟨ t, ht₁, ht₂ ⟩ ;

/-
Forward `n`-step solution: existence of a solution on `[0, n * globalStep K]`
by induction on `n`, chaining one-step solutions and gluing at junctions.
-/
private lemma picard_forward_n
    (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y))
    (y₀ : ℝ) : ∀ n : ℕ,
    ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Icc 0 ((n : ℝ) * globalStep K),
        HasDerivWithinAt y (f t (y t)) (Icc 0 (↑n * globalStep K)) t := by
  -- We proceed by induction on n.
  intro n
  induction' n with n ih;
  · use fun _ => y₀; simp [HasDerivWithinAt];
    simp +decide [ hasDerivAtFilter_iff_tendsto ];
    rw [ Metric.tendsto_nhds ] ; aesop;
  · obtain ⟨ y, hy₁, hy₂ ⟩ := ih
    obtain ⟨ y₂, hy₃, hy₄ ⟩ := picard_one_step f K hK_lip hf_cont (n * globalStep K) (y (n * globalStep K));
    refine' ⟨ fun t => if t ≤ n * globalStep K then y t else y₂ t, _, _ ⟩ <;> norm_num at *;
    · rw [ if_pos ( by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by exact div_nonneg zero_le_one ( by positivity ) ) ), hy₁ ];
    · intro t ht₁ ht₂; split_ifs with h;
      · by_cases h' : t = n * globalStep K;
        · have h_deriv : HasDerivWithinAt y (f t (y t)) (Icc 0 (n * globalStep K)) t ∧ HasDerivWithinAt y₂ (f t (y₂ t)) (Icc (n * globalStep K) ((n + 1) * globalStep K)) t := by
            grind;
          have h_deriv_union : HasDerivWithinAt (fun t => if t ≤ n * globalStep K then y t else y₂ t) (f t (y t)) (Icc 0 (n * globalStep K) ∪ Icc (n * globalStep K) ((n + 1) * globalStep K)) t := by
            rw [ hasDerivWithinAt_iff_tendsto ] at *;
            rw [ hasDerivWithinAt_iff_tendsto ] at h_deriv;
            rw [ nhdsWithin_union ];
            rw [ Filter.tendsto_sup ];
            constructor;
            · refine' h_deriv.1.congr' _;
              filter_upwards [ self_mem_nhdsWithin ] with x' hx' using by rw [ if_pos hx'.2, if_pos h ] ;
            · refine' h_deriv.2.congr' _;
              filter_upwards [ self_mem_nhdsWithin ] with x' hx' ; split_ifs <;> simp_all +decide [ add_mul ];
              exact Or.inr ( by linarith );
          convert h_deriv_union.mono _ using 1;
          exact fun x hx => if h : x ≤ n * globalStep K then Or.inl ⟨ hx.1, h ⟩ else Or.inr ⟨ by linarith [ hx.1 ], hx.2 ⟩;
        · have := hy₂ t ht₁ h;
          rw [ hasDerivWithinAt_iff_tendsto ] at *;
          rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
          intro ε hε; rcases this ε hε with ⟨ δ, hδ, H ⟩ ; use Min.min δ ( ( n : ℝ ) * globalStep K - t ) ; norm_num [ hδ, h' ];
          exact ⟨ lt_of_le_of_ne h h', fun x hx₁ hx₂ hx₃ hx₄ => by rw [ if_pos ( by linarith [ abs_lt.mp hx₄ ] ), if_pos h ] ; simpa [ abs_mul, abs_inv ] using H ⟨ hx₁, by linarith [ abs_lt.mp hx₄ ] ⟩ hx₃ ⟩;
      · have := hy₄ t ( by linarith ) ( by linarith );
        rw [ hasDerivWithinAt_iff_tendsto ] at *;
        rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
        intro ε hε; obtain ⟨ δ, hδ, H ⟩ := this ε hε; use Min.min δ ( t - n * globalStep K ) ; norm_num [ h ];
        exact ⟨ ⟨ hδ, lt_of_not_ge h ⟩, fun x hx₁ hx₂ hx₃ hx₄ => by rw [ if_neg ( by linarith [ abs_lt.mp hx₄ ] ) ] ; simpa [ abs_mul, abs_inv ] using H ⟨ by linarith [ abs_lt.mp hx₄ ], by linarith [ abs_lt.mp hx₄ ] ⟩ hx₃ ⟩

/-
Forward existence on `[0, T]` for arbitrary `T ≥ 0`.
Takes `n = ⌈T / globalStep K⌉` and restricts the `n`-step solution.
-/
private lemma picard_forward_exists
    (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y))
    (y₀ T : ℝ) (hT : 0 ≤ T) :
    ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt y (f t (y t)) (Icc 0 T) t := by
  -- Apply `picard_forward_n` to obtain a sequence of solutions on longer intervals.
  have h_seq : ∀ n : ℕ, ∃ y : ℝ → ℝ, y 0 = y₀ ∧ ∀ t ∈ Icc 0 ((n : ℝ) * globalStep K), HasDerivWithinAt y (f t (y t)) (Icc 0 ((n : ℝ) * globalStep K)) t := by
    exact?;
  -- Choose n such that n * globalStep K ≥ T.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℝ) * globalStep K ≥ T := by
    exact ⟨ ⌈T / globalStep K⌉₊, by nlinarith [ Nat.le_ceil ( T / globalStep K ), show 0 < globalStep K from one_div_pos.mpr ( by positivity ), mul_div_cancel₀ T ( ne_of_gt ( show 0 < globalStep K from one_div_pos.mpr ( by positivity ) ) ) ] ⟩;
  obtain ⟨ y, hy₀, hy ⟩ := h_seq n; exact ⟨ y, hy₀, fun t ht => HasDerivWithinAt.mono ( hy t ⟨ ht.1, ht.2.trans hn ⟩ ) ( Set.Icc_subset_Icc_right hn ) ⟩ ;

/-
Backward existence on `[-T, 0]` for arbitrary `T ≥ 0`.
Uses the forward existence applied to the time-reversed vector field
`g(s, x) = -f(-s, x)` and the substitution `y(t) = z(-t)`.
-/
private lemma picard_backward_exists
    (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y))
    (y₀ T : ℝ) (hT : 0 ≤ T) :
    ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Icc (-T) 0, HasDerivWithinAt y (f t (y t)) (Icc (-T) 0) t := by
  obtain ⟨ z, hz₁, hz₂ ⟩ := picard_forward_exists ( fun s x => -f ( -s ) x ) K ( fun s => by
    convert hK_lip ( -s ) |> LipschitzWith.neg using 1 ) ( fun x => by
    exact Continuous.neg ( hf_cont x |> Continuous.comp <| ContinuousNeg.continuous_neg ) ) y₀ T hT;
  refine' ⟨ fun t => z ( -t ), _, _ ⟩ <;> simp_all +decide [ hasDerivWithinAt_iff_tendsto ];
  intro t ht₁ ht₂; specialize hz₂ ( -t ) ( by linarith ) ( by linarith ) ; simp_all +decide [ Metric.tendsto_nhdsWithin_nhds ] ;
  intro ε hε; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := hz₂ ε hε; use δ, hδ₁; intro x hx₁ hx₂ hx₃; convert hδ₂ ( show 0 ≤ -x by linarith ) ( show -x ≤ T by linarith ) ( by simpa [ dist_neg ] using hx₃ ) using 1 ; ring;
  rw [ show -x + t = - ( x - t ) by ring, abs_neg ] ; ring

/-
Existence of a solution on `[-T, T]` for arbitrary `T ≥ 0`,
by gluing a forward solution on `[0, T]` and backward solution on `[-T, 0]`
at `t = 0`, then using the union property of `HasDerivWithinAt`.
-/
private lemma picard_symmetric_exists
    (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y))
    (y₀ T : ℝ) (hT : 0 ≤ T) :
    ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt y (f t (y t)) (Icc (-T) T) t := by
  obtain ⟨y_forward, hy_forward⟩ := picard_forward_exists f K hK_lip hf_cont y₀ T hT
  obtain ⟨y_backward, hy_backward⟩ := picard_backward_exists f K hK_lip hf_cont y₀ T hT;
  use fun t => if t ≥ 0 then y_forward t else y_backward t;
  refine' ⟨ _, fun t ht => _ ⟩ <;> simp_all +decide [ hasDerivWithinAt_iff_tendsto ];
  by_cases ht_nonneg : 0 ≤ t;
  · by_cases ht_zero : t = 0;
    · rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
      intro ε hε; rcases Metric.tendsto_nhdsWithin_nhds.mp ( hy_forward.2 0 le_rfl hT ) ε hε with ⟨ δ₁, hδ₁, H₁ ⟩ ; rcases Metric.tendsto_nhdsWithin_nhds.mp ( hy_backward.2 0 ( by linarith ) ( by linarith ) ) ε hε with ⟨ δ₂, hδ₂, H₂ ⟩ ; use Min.min δ₁ δ₂; simp_all +decide ;
      intro x hx₁ hx₂ hx₃ hx₄; split_ifs <;> [ exact H₁ ( by linarith ) ( by linarith ) hx₃; exact H₂ ( by linarith ) ( by linarith ) hx₄ ] ;
    · have := hy_forward.2 t ht_nonneg ht.2;
      rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
      intro ε hε; rcases this ε hε with ⟨ δ, hδ, H ⟩ ; use Min.min δ t; simp_all +decide [ abs_of_nonneg, dist_eq_norm ] ;
      exact ⟨ lt_of_le_of_ne ht_nonneg ( Ne.symm ht_zero ), fun x hx₁ hx₂ hx₃ hx₄ => by rw [ if_pos ( by linarith [ abs_lt.mp hx₄ ] ) ] ; exact H ( by linarith [ abs_lt.mp hx₄ ] ) hx₂ hx₃ ⟩;
  · have := hy_backward.2 t ht.1 ( by linarith );
    rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
    intro ε hε; rcases this ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ Min.min δ ( -t ), lt_min hδ ( by linarith ), fun x hx hx' => by rw [ if_neg ( by linarith [ abs_lt.mp hx', min_le_left δ ( -t ), min_le_right δ ( -t ) ] ), if_neg ( by linarith ) ] ; exact H ⟨ by linarith [ abs_lt.mp hx', min_le_left δ ( -t ), min_le_right δ ( -t ), hx.1 ], by linarith [ abs_lt.mp hx', min_le_left δ ( -t ), min_le_right δ ( -t ), hx.2 ] ⟩ ( by aesop ) ⟩ ;

/-! ### Corrected Picard-Lindelöf global theorem -/

/-
**Global ODE existence**: given `f` globally Lipschitz in `y` and continuous in `t`,
the IVP `y' = f(t, y)`, `y(0) = y₀` has a global solution on all of `ℝ`.

The proof constructs solutions on `[-(n+1), n+1]` for each `n : ℕ` using
`picard_symmetric_exists`, then defines the global solution by evaluating
the `n`-th solution at each point `t` with `n > |t|`. Consistency
(solutions on different intervals agree on their common domain) follows
from the Gronwall-based uniqueness theorem `ODE_solution_unique_of_mem_Icc`.
`HasDerivAt` at each `t` follows because `t` lies in the interior of the
interval `[-(n+1), n+1]`, so `HasDerivWithinAt` upgrades to `HasDerivAt`.
-/
theorem picard_lindelof_global_existence
    (f : ℝ → ℝ → ℝ) (y₀ : ℝ)
    (K : NNReal) (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y)) :
    ∃ y : ℝ → ℝ,
      (∀ t : ℝ, HasDerivAt y (f t (y t)) t) ∧ y 0 = y₀ := by
  -- For each n : ℕ, apply picard_symmetric_exists to get sol_n on [-(n+1), n+1] with sol_n 0 = y₀ and HasDerivWithinAt on Icc (-(n+1)) (n+1).
  have h_sol_exists : ∀ n : ℕ, ∃ sol_n : ℝ → ℝ, sol_n 0 = y₀ ∧ (∀ t ∈ Set.Icc (-(n + 1) : ℝ) (n + 1), HasDerivWithinAt sol_n (f t (sol_n t)) (Set.Icc (-(n + 1) : ℝ) (n + 1)) t) := by
    exact fun n => picard_symmetric_exists f K hK_lip hf_cont y₀ ( n + 1 ) ( by linarith );
  choose sol_n h_sol_n₀ h_sol_n using h_sol_exists;
  -- Show that the solutions agree on their common domains.
  have h_sol_agree : ∀ n m : ℕ, n ≤ m → ∀ t ∈ Set.Icc (-(n + 1) : ℝ) (n + 1), sol_n n t = sol_n m t := by
    intros n m hnm t ht;
    apply ODE_solution_unique_of_mem_Icc;
    rotate_left;
    exact ⟨ show ( - ( n + 1 ) : ℝ ) < 0 by linarith, show ( 0 : ℝ ) < n + 1 by linarith ⟩;
    exact fun t ht => ( h_sol_n n t ht |> HasDerivWithinAt.continuousWithinAt );
    exact fun t ht => HasDerivWithinAt.hasDerivAt ( h_sol_n n t <| Set.Ioo_subset_Icc_self ht ) <| Icc_mem_nhds ht.1 ht.2;
    exact fun t ht => Set.mem_univ _;
    exact ContinuousOn.mono ( show ContinuousOn ( sol_n m ) ( Icc ( - ( m + 1 ) : ℝ ) ( m + 1 ) ) from fun t ht => ( h_sol_n m t ht |> HasDerivWithinAt.continuousWithinAt ) ) ( Set.Icc_subset_Icc ( by linarith [ show ( n : ℝ ) ≤ m by norm_cast ] ) ( by linarith [ show ( n : ℝ ) ≤ m by norm_cast ] ) );
    exact fun t ht => HasDerivWithinAt.hasDerivAt ( h_sol_n m t ⟨ by linarith [ ht.1, show ( n : ℝ ) ≤ m by norm_cast ], by linarith [ ht.2, show ( n : ℝ ) ≤ m by norm_cast ] ⟩ ) ( Icc_mem_nhds ( by linarith [ ht.1, show ( n : ℝ ) ≤ m by norm_cast ] ) ( by linarith [ ht.2, show ( n : ℝ ) ≤ m by norm_cast ] ) );
    all_goals norm_num;
    exacts [ by rw [ h_sol_n₀, h_sol_n₀ ], ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩, K, fun t ht₁ ht₂ => hK_lip t ];
  -- Define the global solution y by taking the value of sol_n at each point t.
  use fun t => sol_n (Nat.ceil (|t|)) t;
  refine' ⟨ fun t => _, _ ⟩;
  · have h_sol_eq : ∀ᶠ s in nhds t, sol_n (Nat.ceil (|s|)) s = sol_n (Nat.ceil (|t|) + 1) s := by
      filter_upwards [ Metric.ball_mem_nhds t zero_lt_one ] with s hs;
      apply h_sol_agree;
      · exact Nat.ceil_le.mpr ( by norm_num; cases abs_cases s <;> cases abs_cases t <;> linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hs ), Nat.le_ceil ( |t| ) ] );
      · constructor <;> cases abs_cases s <;> linarith [ Nat.le_ceil ( |s| ) ];
    have h_sol_eq : HasDerivAt (fun s => sol_n (Nat.ceil (|t|) + 1) s) (f t (sol_n (Nat.ceil (|t|) + 1) t)) t := by
      convert h_sol_n ( ⌈|t|⌉₊ + 1 ) t _ |> HasDerivWithinAt.hasDerivAt <| ?_ using 1;
      · constructor <;> push_cast <;> cases abs_cases t <;> linarith [ Nat.le_ceil ( |t| ) ];
      · exact Icc_mem_nhds ( by push_cast; cases abs_cases t <;> linarith [ Nat.le_ceil ( |t| ) ] ) ( by push_cast; cases abs_cases t <;> linarith [ Nat.le_ceil ( |t| ) ] );
    convert h_sol_eq.congr_of_eventuallyEq ‹_› using 1;
    exact congr_arg _ ( h_sol_agree _ _ ( Nat.le_succ _ ) _ ⟨ by cases abs_cases t <;> linarith [ Nat.le_ceil ( |t| ) ], by cases abs_cases t <;> linarith [ Nat.le_ceil ( |t| ) ] ⟩ );
  · norm_num [ h_sol_n₀ ]

/-- **Picard-Lindelöf global existence + uniqueness** (corrected).

Compared to the original scaffold, this version replaces the
measurability and integrability hypotheses with continuity of `f` in
`t`. When `f` is globally Lipschitz in `y` and continuous in `t`, the
IVP has a unique solution on all of `ℝ`.

**Uniqueness** is proved using Gronwall's inequality
(`ODE_solution_unique_univ` from Mathlib).
**Existence** is proved in `picard_lindelof_global_existence` above. -/
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
    obtain ⟨y, hy_deriv, hy_init⟩ := picard_lindelof_global_existence f y₀ K hK_lip hf_cont
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