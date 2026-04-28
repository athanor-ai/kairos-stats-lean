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

/-! ### Helper lemmas for asymptotic stability -/

/-- The Lie derivative condition `V'(y)·f(y) < 0` for `y ≠ 0` implies `f` has no
fixed points other than `0`. -/
private lemma f_no_other_zeros
    (f : ℝ → ℝ) (V : ℝ → ℝ)
    (h_lie_strict : ∀ y : ℝ, y ≠ 0 → deriv V y * f y < 0) :
    ∀ y : ℝ, y ≠ 0 → f y ≠ 0 := by
  intro y hy hf
  have := h_lie_strict y hy
  simp [hf] at this

/-- V ∘ y is antitone on [0, ∞) when the Lie derivative is non-positive. -/
private lemma V_comp_y_antitone
    (f : ℝ → ℝ) (V : ℝ → ℝ) (y : ℝ → ℝ)
    (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_lie : ∀ y : ℝ, deriv V y * f y ≤ 0)
    (hy_ode : ∀ t : ℝ, HasDerivAt y (f (y t)) t) :
    AntitoneOn (V ∘ y) (Set.Ici 0) := by
  have h_V_y_diff : ∀ u : ℝ, HasDerivAt (V ∘ y) (deriv V (y u) * f (y u)) u := by
    intro u
    exact (h_V_diff (y u)).hasDerivAt.comp u (hy_ode u)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun u _ => ((h_V_y_diff u).continuousAt).continuousWithinAt
  · exact fun u _ => ((h_V_y_diff u).differentiableAt).differentiableWithinAt
  · intro u _; rw [(h_V_y_diff u).deriv]; exact h_lie (y u)

/-
V(y(t)) converges as t → ∞ (antitone + bounded below by 0).
-/
private lemma V_comp_y_tendsto
    (f : ℝ → ℝ) (V : ℝ → ℝ) (y : ℝ → ℝ)
    (h_V_zero : V 0 = 0)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_lie : ∀ y : ℝ, deriv V y * f y ≤ 0)
    (hy_ode : ∀ t : ℝ, HasDerivAt y (f (y t)) t) :
    ∃ L : ℝ, Filter.Tendsto (fun t => V (y t)) Filter.atTop (nhds L) ∧ 0 ≤ L := by
  -- By assumption, $V(y(t))$ is antitone and bounded below by $0$.
  have h_antitone : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → V (y t₂) ≤ V (y t₁) := by
    intros t₁ t₂ ht₁ ht₂
    have h_antitone : AntitoneOn (V ∘ y) (Set.Ici 0) := by
      apply V_comp_y_antitone f V y h_V_diff h_lie hy_ode;
    exact h_antitone ht₁ ( show 0 ≤ t₂ by linarith ) ht₂;
  -- Since $V(y(t))$ is antitone and bounded below by $0$, it converges to some limit $L \geq 0$.
  have h_conv : Filter.Tendsto (fun t => V (y t)) Filter.atTop (nhds (sInf (Set.image (fun t => V (y t)) (Set.Ici 0)))) := by
    apply_rules [ tendsto_order.2 ⟨ _, _ ⟩ ];
    · exact fun x hx => Filter.eventually_atTop.mpr ⟨ 0, fun t ht => lt_of_lt_of_le hx <| csInf_le ⟨ 0, Set.forall_mem_image.mpr fun t ht => by by_cases h : y t = 0 <;> simpa [ * ] using le_of_lt ( h_V_pos _ h ) ⟩ <| Set.mem_image_of_mem _ ht ⟩;
    · exact fun x hx => by rcases exists_lt_of_csInf_lt ( Set.Nonempty.image _ <| Set.nonempty_Ici ) hx with ⟨ z, ⟨ t, ht, rfl ⟩, hz ⟩ ; filter_upwards [ Filter.eventually_ge_atTop t ] with u hu using lt_of_le_of_lt ( h_antitone _ _ ht hu ) hz;
  exact ⟨ _, h_conv, le_csInf ( Set.Nonempty.image _ <| Set.nonempty_Ici ) <| Set.forall_mem_image.2 fun t ht => le_of_not_gt fun h => by linarith [ h_V_pos ( y t ) <| by contrapose! h; aesop ] ⟩

/-
If V(y(t)) → 0, positive-definiteness of V gives y(t) → 0.
-/
private lemma y_tendsto_zero_of_V_tendsto_zero
    (V : ℝ → ℝ) (y : ℝ → ℝ)
    (h_V_zero : V 0 = 0)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (hy_cont : Continuous y)
    (hy_bound : ∃ B : ℝ, ∀ t : ℝ, t ≥ 0 → |y t| ≤ B)
    (hV_tendsto : Filter.Tendsto (fun t => V (y t)) Filter.atTop (nhds 0)) :
    Filter.Tendsto y Filter.atTop (nhds 0) := by
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε;
  -- Since $V$ is continuous and positive on $\{x : |x| = \epsilon\}$, let $m = \min(V(\epsilon), V(-\epsilon)) > 0$.
  obtain ⟨m, hm⟩ : ∃ m > 0, ∀ x, abs x ≥ ε / 2 ∧ abs x ≤ hy_bound.choose → V x ≥ m := by
    have h_compact : IsCompact {x : ℝ | abs x ≥ ε / 2 ∧ abs x ≤ hy_bound.choose} := by
      refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
      exact ⟨ isClosed_Icc.preimage continuous_abs, isBounded_iff_forall_norm_le.mpr ⟨ hy_bound.choose, fun x hx => hx.2 ⟩ ⟩;
    by_cases h_empty : {x : ℝ | abs x ≥ ε / 2 ∧ abs x ≤ hy_bound.choose} = ∅;
    · exact ⟨ 1, zero_lt_one, fun x hx => False.elim <| h_empty.subset hx ⟩;
    · obtain ⟨ m, hm ⟩ := h_compact.exists_isMinOn ( Set.nonempty_iff_ne_empty.mpr h_empty ) ( show ContinuousOn V _ from continuousOn_of_forall_continuousAt fun x hx => DifferentiableAt.continuousAt ( h_V_diff x ) );
      exact ⟨ V m, h_V_pos m ( by rintro rfl; exact absurd hm.1.1 ( by norm_num; linarith ) ), fun x hx => hm.2 hx ⟩;
  filter_upwards [ hV_tendsto m hm.1, Filter.eventually_ge_atTop 0 ] with t ht₁ ht₂;
  contrapose! hm;
  exact fun _ => ⟨ y t, ⟨ by norm_num at hm; linarith, hy_bound.choose_spec t ht₂ ⟩, by linarith [ abs_lt.mp ht₁ ] ⟩

/-
Key lemma: in 1D with continuous f, a monotone bounded trajectory y
with y' = f(y) and f having no zeros except 0 must converge to 0.
-/
private lemma monotone_trajectory_tends_to_zero
    (f : ℝ → ℝ) (h_f_cont : Continuous f) (h_zero : f 0 = 0)
    (h_f_ne : ∀ y : ℝ, y ≠ 0 → f y ≠ 0)
    (y : ℝ → ℝ) (hy_ode : ∀ t : ℝ, HasDerivAt y (f (y t)) t)
    (hy_bound : ∃ B : ℝ, ∀ t : ℝ, t ≥ 0 → |y t| ≤ B)
    (hy_pos : ∀ t : ℝ, t ≥ 0 → y t > 0)
    (hy_mono : AntitoneOn y (Set.Ici (0 : ℝ))) :
    Filter.Tendsto y Filter.atTop (nhds 0) := by
  -- y is antitone on [0,∞) (by hy_mono) and positive (by hy_pos), so y is bounded below by 0. By monotone convergence (antitone bounded below), y → L' for some L' ≥ 0.
  obtain ⟨L', hL'⟩ : ∃ L', Filter.Tendsto y Filter.atTop (nhds L') ∧ 0 ≤ L' := by
    have hL'_conv : Filter.Tendsto (fun t => y t) Filter.atTop (nhds (sInf (y '' Set.Ici 0))) := by
      apply_rules [ tendsto_order.2 ⟨ _, _ ⟩ ];
      · exact fun x hx => Filter.eventually_atTop.mpr ⟨ 0, fun t ht => lt_of_lt_of_le hx <| csInf_le ⟨ 0, Set.forall_mem_image.mpr fun t ht => le_of_lt <| hy_pos t ht ⟩ <| Set.mem_image_of_mem _ ht ⟩;
      · exact fun x hx => by rcases exists_lt_of_csInf_lt ( Set.Nonempty.image _ <| Set.nonempty_Ici ) hx with ⟨ z, ⟨ t, ht, rfl ⟩, hz ⟩ ; filter_upwards [ Filter.eventually_ge_atTop t ] with u hu using lt_of_le_of_lt ( hy_mono ( show 0 ≤ t by linarith [ Set.mem_Ici.mp ht ] ) ( show 0 ≤ u by linarith [ Set.mem_Ici.mp ht ] ) hu ) hz;
    exact ⟨ _, hL'_conv, le_csInf ( Set.Nonempty.image _ <| Set.nonempty_Ici ) <| Set.forall_mem_image.2 fun t ht => le_of_lt <| hy_pos t ht ⟩;
  -- Since $y$ is antitone and $y(t) \to L'$, we have $y'(t) = f(y(t)) \to f(L')$.
  have h_deriv_tendsto : Filter.Tendsto (fun t => (y (t + 1) - y t) / 1) Filter.atTop (nhds (f L')) := by
    have h_deriv_tendsto : Filter.Tendsto (fun t => deriv y t) Filter.atTop (nhds (f L')) := by
      simpa only [ hy_ode _ |> HasDerivAt.deriv ] using h_f_cont.continuousAt.tendsto.comp hL'.1;
    -- By the Mean Value Theorem, there exists some $c_t \in (t, t+1)$ such that $(y(t+1) - y(t)) / 1 = deriv y(c_t)$.
    have h_mvt : ∀ t ≥ 0, ∃ c_t ∈ Set.Ioo t (t + 1), (y (t + 1) - y t) / 1 = deriv y c_t := by
      intro t ht; have := exists_deriv_eq_slope y ( by linarith : t < t + 1 ) ; norm_num at *;
      exact this ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy_ode x ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( hy_ode x |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, hc₂.symm ⟩;
    choose! c hc using h_mvt;
    exact Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 0 ] with t ht; aesop ) ( h_deriv_tendsto.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Max.max x 0, fun t ht => by linarith [ hc t ( by linarith [ le_max_left x 0, le_max_right x 0 ] ) |>.1.1, le_max_left x 0, le_max_right x 0 ] ⟩ );
  by_cases hL'_zero : L' = 0 <;> simp_all +decide [ div_eq_inv_mul ];
  exact absurd ( tendsto_nhds_unique h_deriv_tendsto ( Filter.Tendsto.sub ( hL'.1.comp ( Filter.tendsto_id.atTop_add tendsto_const_nhds ) ) hL'.1 ) ) ( by aesop )

/-
Asymptotic stability: when the Lie derivative is *strictly*
negative away from the equilibrium, trajectories not only stay near
zero but converge to it.

**Corrected statement**: the original scaffold omitted `Continuous f`,
which is necessary — without it, a discontinuous `f` can produce
bounded trajectories that converge to a nonzero limit `L` with
`f(L) ≠ 0` while keeping the Lie derivative strictly negative.
With `Continuous f`, the standard 1-D monotonicity argument applies:
`f` has no zeros other than `0` (from the strict Lie condition), so
any trajectory is eventually monotone; a monotone bounded trajectory
converges to a zero of `f`, which must be `0`.
-/
theorem lyapunov_asymptotic
    (f : ℝ → ℝ) (h_zero : f 0 = 0)
    (h_f_cont : Continuous f)
    (V : ℝ → ℝ) (h_V_zero : V 0 = 0)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_lie_strict : ∀ y : ℝ, y ≠ 0 → deriv V y * f y < 0) :
    ∃ δ > 0, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) →
      |y 0| < δ →
      Filter.Tendsto y Filter.atTop (nhds 0) := by
  -- Apply Lyapunov stability to get δ₀ > 0: |y(0)| < δ₀ ⇒ |y(t)| < 1 for all t ≥ 0.
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ : ∃ δ₀ > 0, ∀ (y : ℝ → ℝ),
    (∀ t : ℝ, HasDerivAt y (f (y t)) t) →
    |y 0| < δ₀ →
    ∀ t ≥ (0 : ℝ), |y t| < 1 := by
      apply lyapunov_stable f h_zero V h_V_zero h_V_pos h_V_diff (fun y => le_of_lt_or_eq (by
      grind)) 1 (by norm_num);
  -- Set δ = δ₀. Fix y with |y(0)| < δ.
  use δ₀, hδ₀_pos;
  intro y hy hy₀
  by_contra h_contra
  have hL : ∃ L, Filter.Tendsto (fun t => V (y t)) Filter.atTop (nhds L) ∧ 0 < L := by
    have hL : ∃ L, Filter.Tendsto (fun t => V (y t)) Filter.atTop (nhds L) ∧ 0 ≤ L := by
      apply_rules [ V_comp_y_tendsto ];
      exact fun x => if hx : x = 0 then by norm_num [ hx, h_zero, h_V_zero ] else le_of_lt ( h_lie_strict x hx );
    obtain ⟨ L, hL₁, hL₂ ⟩ := hL;
    by_cases hL_zero : L = 0;
    · have := y_tendsto_zero_of_V_tendsto_zero V y h_V_zero h_V_pos h_V_diff ( show Continuous y from continuous_iff_continuousAt.mpr fun t => HasDerivAt.continuousAt ( hy t ) ) ⟨ 1, fun t ht => le_of_lt ( hδ₀ y hy hy₀ t ht ) ⟩ ; aesop;
    · exact ⟨ L, hL₁, lt_of_le_of_ne hL₂ ( Ne.symm hL_zero ) ⟩;
  obtain ⟨ L, hL₁, hL₂ ⟩ := hL
  have hL₃ : ∀ t ≥ 0, y t ≠ 0 := by
    intro t ht h; have := hL₁.eventually ( lt_mem_nhds hL₂ ) ; have := this.and ( Filter.eventually_ge_atTop t ) ; obtain ⟨ u, hu₁, hu₂ ⟩ := this.exists; simp_all +decide [ ne_of_gt ] ;
    have h_contra : ∀ s ∈ Set.Icc t u, V (y s) ≤ V (y t) := by
      intros s hs; exact (by
      have h_contra : AntitoneOn (fun t => V (y t)) (Set.Ici 0) := by
        apply_rules [ V_comp_y_antitone ];
        exact fun x => if hx : x = 0 then by simp +decide [ * ] else le_of_lt ( h_lie_strict x hx );
      exact h_contra ( show 0 ≤ t by linarith ) ( show 0 ≤ s by linarith [ hs.1 ] ) hs.1);
    grind +splitImp
  have hL₄ : ∀ t ≥ 0, f (y t) ≠ 0 := by
    exact fun t ht => fun h => by simpa [ * ] using h_lie_strict ( y t ) ( hL₃ t ht ) ;
  have hL₅ : ∀ t ≥ 0, deriv V (y t) ≠ 0 := by
    exact fun t ht => fun h => by simpa [ h, hL₄ t ht ] using h_lie_strict ( y t ) ( hL₃ t ht ) ;
  have hL₆ : ∀ t ≥ 0, deriv (fun t => V (y t)) t < 0 := by
    intro t ht; rw [ show deriv ( fun t => V ( y t ) ) t = deriv V ( y t ) * deriv y t by exact deriv_comp t ( h_V_diff _ ) ( hy _ |> HasDerivAt.differentiableAt ) ] ; rw [ hy _ |> HasDerivAt.deriv ] ; nlinarith [ h_lie_strict ( y t ) ( hL₃ t ht ) ] ;
  have hL₇ : AntitoneOn (fun t => V (y t)) (Set.Ici 0) := by
    apply_rules [ antitoneOn_of_deriv_nonpos ];
    · exact convex_Ici _;
    · exact continuousOn_of_forall_continuousAt fun t ht => DifferentiableAt.continuousAt ( h_V_diff _ |> DifferentiableAt.comp _ <| hy _ |> HasDerivAt.differentiableAt );
    · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.comp t ( h_V_diff _ ) ( hy _ |> HasDerivAt.differentiableAt ) );
    · exact fun t ht => le_of_lt ( hL₆ t <| interior_subset ht )
  have hL₈ : ∃ L', Filter.Tendsto y Filter.atTop (nhds L') := by
    have hL₈ : StrictMonoOn y (Set.Ici 0) ∨ StrictAntiOn y (Set.Ici 0) := by
      have hL₈ : ∀ t ≥ 0, deriv y t > 0 ∨ deriv y t < 0 := by
        exact fun t ht => Or.symm <| lt_or_gt_of_ne <| by simpa [ hy t |> HasDerivAt.deriv ] using hL₄ t ht;
      have hL₉ : (∀ t ≥ 0, deriv y t > 0) ∨ (∀ t ≥ 0, deriv y t < 0) := by
        have hL₉ : IsConnected (Set.image (fun t => deriv y t) (Set.Ici 0)) := by
          apply_rules [ IsConnected.image, isConnected_Ici ];
          exact ContinuousOn.congr ( show ContinuousOn ( fun t => f ( y t ) ) ( Set.Ici 0 ) from h_f_cont.comp_continuousOn ( show ContinuousOn y ( Set.Ici 0 ) from continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hy t ) ) ) fun t ht => HasDerivAt.deriv ( hy t ) ▸ rfl;
        contrapose! hL₉;
        obtain ⟨ ⟨ t₁, ht₁₁, ht₁₂ ⟩, ⟨ t₂, ht₂₁, ht₂₂ ⟩ ⟩ := hL₉; exact fun h => by have := h.Icc_subset ( Set.mem_image_of_mem _ ht₁₁ ) ( Set.mem_image_of_mem _ ht₂₁ ) ⟨ ht₁₂, ht₂₂ ⟩ ; obtain ⟨ u, hu₁, hu₂ ⟩ := this; specialize hL₈ u hu₁; cases hL₈ <;> linarith;
      have hL₁₀ : StrictMonoOn y (Set.Ici 0) ∨ StrictAntiOn y (Set.Ici 0) := by
        rcases hL₉ with h | h <;> [ left; right ] <;> intro t ht u hu htu <;> have := exists_deriv_eq_slope y htu <;> simp_all +decide [ StrictMonoOn, StrictAntiOn ] ;
        · exact this ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy x ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( hy x |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by nlinarith [ h c ( by linarith ), mul_div_cancel₀ ( y u - y t ) ( sub_ne_zero_of_ne htu.ne' ) ] ;
        · exact this ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy x ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( hy x |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by nlinarith [ h c ( by linarith ), mul_div_cancel₀ ( y u - y t ) ( sub_ne_zero_of_ne htu.ne' ) ] ;
      exact hL₁₀;
    cases' hL₈ with hL₈ hL₈;
    · have hL₈ : BddAbove (Set.image y (Set.Ici 0)) := by
        exact ⟨ 1, Set.forall_mem_image.2 fun t ht => le_of_abs_le <| le_of_lt <| hδ₀ y hy hy₀ t ht ⟩;
      have hL₈ : Filter.Tendsto y Filter.atTop (nhds (sSup (Set.image y (Set.Ici 0)))) := by
        apply_rules [ tendsto_order.2 ⟨ _, _ ⟩ ];
        · exact fun x hx => by rcases exists_lt_of_lt_csSup ( Set.Nonempty.image _ <| Set.nonempty_Ici ) hx with ⟨ z, ⟨ t, ht, rfl ⟩, hz ⟩ ; filter_upwards [ Filter.eventually_ge_atTop t ] with u hu using hz.trans_le <| ‹StrictMonoOn y ( Set.Ici 0 ) ›.monotoneOn ( show 0 ≤ t by linarith [ Set.mem_Ici.mp ht ] ) ( show 0 ≤ u by linarith [ Set.mem_Ici.mp ht ] ) hu;
        · exact fun x hx => Filter.eventually_atTop.mpr ⟨ 0, fun t ht => lt_of_le_of_lt ( le_csSup hL₈ <| Set.mem_image_of_mem _ ht ) hx ⟩;
      exact ⟨ _, hL₈ ⟩;
    · have hL₈ : Filter.Tendsto y Filter.atTop (nhds (sInf { y t | t ≥ 0 })) := by
        apply_rules [ tendsto_order.2 ⟨ _, _ ⟩ ];
        · exact fun x hx => Filter.eventually_atTop.mpr ⟨ 0, fun t ht => lt_of_lt_of_le hx <| csInf_le ⟨ -1, by rintro x ⟨ u, hu, rfl ⟩ ; linarith [ abs_lt.mp <| hδ₀ y hy hy₀ u hu ] ⟩ ⟨ t, ht, rfl ⟩ ⟩;
        · exact fun x hx => by rcases exists_lt_of_csInf_lt ( by exact ⟨ _, ⟨ 0, by norm_num, rfl ⟩ ⟩ ) hx with ⟨ z, ⟨ t, ht, rfl ⟩, hz ⟩ ; filter_upwards [ Filter.eventually_ge_atTop t ] with u hu using lt_of_le_of_lt ( hL₈.antitoneOn ( show 0 ≤ t by linarith ) ( show 0 ≤ u by linarith ) hu ) hz;
      exact ⟨ _, hL₈ ⟩
  obtain ⟨ L', hL' ⟩ := hL₈
  have hL₉ : f L' = 0 := by
    have hL₉ : Filter.Tendsto (fun t => (y (t + 1) - y t) / 1) Filter.atTop (nhds (f L')) := by
      have hL₉ : ∀ t ≥ 0, ∃ c ∈ Set.Ioo t (t + 1), deriv y c = (y (t + 1) - y t) / 1 := by
        intro t ht; have := exists_deriv_eq_slope y ( show t < t + 1 by linarith ) ; norm_num at *;
        exact this ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy x ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( hy x |> HasDerivAt.differentiableAt ) );
      choose! c hc using hL₉;
      have hL₉ : Filter.Tendsto (fun t => f (y (c t))) Filter.atTop (nhds (f L')) := by
        exact h_f_cont.continuousAt.tendsto.comp ( hL'.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Max.max x 0, fun t ht => by linarith [ hc t ( by linarith [ le_max_left x 0, le_max_right x 0 ] ) |>.1.1, le_max_left x 0, le_max_right x 0 ] ⟩ );
      exact hL₉.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 0 ] with t ht; rw [ ← hc t ht |>.2, hy _ |> HasDerivAt.deriv ] );
    exact tendsto_nhds_unique hL₉ ( by simpa using Filter.Tendsto.sub ( hL'.comp ( Filter.tendsto_id.atTop_add tendsto_const_nhds ) ) hL' )
  have hL₁₀ : L' = 0 := by
    exact Classical.not_not.1 fun h => absurd ( h_lie_strict L' h ) ( by norm_num [ hL₉ ] )
  have hL₁₁ : Filter.Tendsto y Filter.atTop (nhds 0) := by
    exact hL₁₀ ▸ hL'
  contradiction

/-! ### Helper lemmas for LaSalle's invariance principle -/

/-
If a trajectory of y' = f(y) goes from above `c` to below `c`, then `f(c) ≤ 0`.
    Proof: at the first time `s₁` the trajectory hits `c` from above,
    the left-derivative is ≤ 0 (since y > c just before s₁), hence
    `f(c) = y'(s₁) ≤ 0`.
-/
private lemma f_nonpos_of_downcrossing
    (f : ℝ → ℝ) (y : ℝ → ℝ) (c : ℝ)
    (hy : ∀ t : ℝ, HasDerivAt y (f (y t)) t)
    {t₁ t₂ : ℝ} (ht : t₁ < t₂) (h1 : c < y t₁) (h2 : y t₂ < c) :
    f c ≤ 0 := by
  -- Let $s₁ = \inf \{ s \in [t₁, t₂] : y(s) ≤ c \}$. This set is nonempty (contains $t₂$) and bounded below (by $t₁$).
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ ∈ Set.Icc t₁ t₂, y s₁ ≤ c ∧ ∀ s ∈ Set.Icc t₁ t₂, s < s₁ → y s > c := by
    have h_inf : ∃ s₁ ∈ {s ∈ Set.Icc t₁ t₂ | y s ≤ c}, ∀ s ∈ {s ∈ Set.Icc t₁ t₂ | y s ≤ c}, s₁ ≤ s := by
      apply_rules [ IsCompact.exists_isLeast, CompactIccSpace.isCompact_Icc ];
      · exact CompactIccSpace.isCompact_Icc.of_isClosed_subset ( isClosed_Icc.inter <| isClosed_le ( show Continuous y from continuous_iff_continuousAt.mpr fun t => HasDerivAt.continuousAt <| hy t ) continuous_const ) fun x hx => hx.1;
      · exact ⟨ t₂, ⟨ ⟨ by linarith, by linarith ⟩, by linarith ⟩ ⟩;
    obtain ⟨ s₁, hs₁₁, hs₁₂ ⟩ := h_inf; exact ⟨ s₁, hs₁₁.1, hs₁₁.2, fun s hs hs' => not_le.1 fun hs'' => hs'.not_ge <| hs₁₂ s ⟨ hs, hs'' ⟩ ⟩ ;
  -- Since y is continuous (from HasDerivAt), the set {s ∈ [t₁, t₂] : y s ≤ c} is closed. So s₁ is in this set: y(s₁) ≤ c.
  have hs₁_eq : y s₁ = c := by
    by_cases hs₁_eq : s₁ = t₁;
    · grind;
    · -- Since $s₁ \neq t₁$, we have $s₁ > t₁$.
      have hs₁_gt : s₁ > t₁ := by
        exact lt_of_le_of_ne hs₁.1.1 ( Ne.symm hs₁_eq );
      -- Since $s₁ > t₁$, we can apply the continuity of $y$ to get that $y(s₁) = \lim_{s \to s₁^-} y(s)$.
      have hs₁_cont : Filter.Tendsto y (nhdsWithin s₁ (Set.Iio s₁)) (nhds (y s₁)) := by
        exact HasDerivAt.continuousAt ( hy s₁ ) |> ContinuousAt.continuousWithinAt;
      exact le_antisymm hs₁.2.1 ( le_of_tendsto_of_tendsto tendsto_const_nhds hs₁_cont <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT hs₁_gt ) fun x hx => le_of_lt <| hs₁.2.2 x ⟨ hx.1.le, hx.2.le.trans hs₁.1.2 ⟩ hx.2 );
  -- For h < 0 small (so s₁ + h ∈ (t₁, s₁)): y(s₁ + h) > c = y(s₁).
  have h_neg : ∀ᶠ h in nhdsWithin 0 (Set.Iio 0), y (s₁ + h) > c := by
    by_cases hs₁_eq_t₁ : s₁ = t₁;
    · grind;
    · rw [ eventually_nhdsWithin_iff ];
      rw [ Metric.eventually_nhds_iff ];
      exact ⟨ s₁ - t₁, sub_pos.mpr ( lt_of_le_of_ne hs₁.1.1 ( Ne.symm hs₁_eq_t₁ ) ), fun x hx₁ hx₂ => hs₁.2.2 _ ⟨ by linarith [ abs_lt.mp hx₁, hx₂.out ], by linarith [ abs_lt.mp hx₁, hx₂.out, hs₁.1.2 ] ⟩ ( by linarith [ abs_lt.mp hx₁, hx₂.out ] ) ⟩;
  -- So (y(s₁ + h) - y(s₁))/h = (positive)/(negative) ≤ 0.
  have h_deriv_neg : Filter.Tendsto (fun h => (y (s₁ + h) - y s₁) / h) (nhdsWithin 0 (Set.Iio 0)) (nhds (f c)) := by
    have := hy s₁;
    simpa [ div_eq_inv_mul, hs₁_eq ] using this.tendsto_slope_zero_left;
  exact le_of_tendsto h_deriv_neg ( by filter_upwards [ h_neg, self_mem_nhdsWithin ] with x hx₁ hx₂ using div_nonpos_of_nonneg_of_nonpos ( by linarith ) hx₂.out.le )

/-
If a trajectory of y' = f(y) goes from below `c` to above `c`, then `f(c) ≥ 0`.
-/
private lemma f_nonneg_of_upcrossing
    (f : ℝ → ℝ) (y : ℝ → ℝ) (c : ℝ)
    (hy : ∀ t : ℝ, HasDerivAt y (f (y t)) t)
    {t₁ t₂ : ℝ} (ht : t₁ < t₂) (h1 : y t₁ < c) (h2 : c < y t₂) :
    0 ≤ f c := by
  -- Let $s₁ = sInf {s ∈ (t₁, t₂] : y(s) ≥ c}$.
  set s₁ := sInf {s | s ∈ Set.Ioc t₁ t₂ ∧ y s ≥ c} with hs₁_def
  have hs₁_mem : s₁ ∈ Set.Icc t₁ t₂ := by
    exact ⟨ le_csInf ⟨ t₂, ⟨ ⟨ by linarith, by linarith ⟩, by linarith ⟩ ⟩ fun x hx => hx.1.1.le, csInf_le ⟨ t₁, fun x hx => hx.1.1.le ⟩ ⟨ ⟨ by linarith, by linarith ⟩, by linarith ⟩ ⟩;
  have hs₁_ge : y s₁ ≥ c := by
    have hs₁_ge_c : ∃ seq : ℕ → ℝ, (∀ n, seq n ∈ Set.Ioc t₁ t₂ ∧ y (seq n) ≥ c) ∧ Filter.Tendsto seq Filter.atTop (nhds s₁) := by
      have hs₁_ge : ∀ ε > 0, ∃ s ∈ {s | s ∈ Set.Ioc t₁ t₂ ∧ y s ≥ c}, |s - s₁| < ε := by
        exact fun ε ε_pos => by rcases exists_lt_of_csInf_lt ( show { s : ℝ | s ∈ Set.Ioc t₁ t₂ ∧ y s ≥ c }.Nonempty from ⟨ t₂, ⟨ by linarith, by linarith ⟩, by linarith ⟩ ) ( lt_add_of_pos_right _ ε_pos ) with ⟨ s, hs₁, hs₂ ⟩ ; exact ⟨ s, hs₁, abs_lt.mpr ⟨ by linarith [ hs₁_mem.1, hs₁_mem.2, csInf_le ⟨ t₁, fun x hx => hx.1.1.le ⟩ hs₁ ], by linarith [ hs₁_mem.1, hs₁_mem.2, csInf_le ⟨ t₁, fun x hx => hx.1.1.le ⟩ hs₁ ] ⟩ ⟩ ;
      exact ⟨ fun n => Classical.choose ( hs₁_ge ( 1 / ( n + 1 ) ) ( by positivity ) ), fun n => Classical.choose_spec ( hs₁_ge ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.1, tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => Classical.choose_spec ( hs₁_ge ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
    obtain ⟨ seq, hseq₁, hseq₂ ⟩ := hs₁_ge_c; exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( Filter.Tendsto.comp ( show Filter.Tendsto y ( nhds s₁ ) ( nhds ( y s₁ ) ) from HasDerivAt.continuousAt ( hy s₁ ) ) hseq₂ ) fun n => hseq₁ n |>.2;
  have hs₁_le : ∀ s ∈ Set.Ioo t₁ s₁, y s < c := by
    intros s hs
    by_contra h_contra
    have hs_mem : s ∈ {s | s ∈ Set.Ioc t₁ t₂ ∧ y s ≥ c} := by
      exact ⟨ ⟨ hs.1, hs.2.le.trans hs₁_mem.2 ⟩, le_of_not_gt h_contra ⟩
    have hs_le : s₁ ≤ s := by
      exact csInf_le ⟨ t₁, fun x hx => hx.1.1.le ⟩ hs_mem
    linarith [hs.2]
  have hs₁_eq : y s₁ = c := by
    have hs₁_eq : Filter.Tendsto y (nhdsWithin s₁ (Set.Iio s₁)) (nhds (y s₁)) := by
      exact HasDerivAt.continuousAt ( hy s₁ ) |> ContinuousAt.continuousWithinAt;
    exact le_antisymm ( le_of_tendsto hs₁_eq <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT <| show t₁ < s₁ from lt_of_le_of_ne hs₁_mem.1 <| Ne.symm <| by rintro h; norm_num [ h ] at * ; linarith ) fun x hx => le_of_lt <| hs₁_le x hx ) hs₁_ge;
  -- By definition of $s₁$, we know that $y'(s₁) = f(c)$.
  have hs₁_deriv : HasDerivAt y (f c) s₁ := by
    simpa only [ hs₁_eq ] using hy s₁;
  have hs₁_deriv_nonneg : Filter.Tendsto (fun h => (y (s₁ + h) - y s₁) / h) (nhdsWithin 0 (Set.Iio 0)) (nhds (f c)) := by
    simpa [ div_eq_inv_mul ] using hs₁_deriv.tendsto_slope_zero_left;
  have hs₁_deriv_nonneg : ∀ᶠ h in nhdsWithin 0 (Set.Iio 0), (y (s₁ + h) - y s₁) / h ≥ 0 := by
    rw [ eventually_nhdsWithin_iff ];
    rw [ Metric.eventually_nhds_iff ];
    by_cases hs₁_eq_t₁ : s₁ = t₁;
    · grind;
    · exact ⟨ s₁ - t₁, sub_pos.mpr ( lt_of_le_of_ne hs₁_mem.1 ( Ne.symm hs₁_eq_t₁ ) ), fun x hx₁ hx₂ => div_nonneg_of_nonpos ( sub_nonpos.mpr <| by linarith [ hs₁_le ( s₁ + x ) ⟨ by linarith [ abs_lt.mp hx₁, hx₂.out ], by linarith [ abs_lt.mp hx₁, hx₂.out ] ⟩ ] ) hx₂.out.le ⟩;
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› hs₁_deriv_nonneg

/-
Every bounded solution of a scalar autonomous ODE `y' = f(y)` with
    `f` continuous converges as `t → ∞`.

    Proof: if `y` does not converge, pick `a < b` in the ω-limit set.
    For any `c ∈ (a,b)`, `y` crosses `c` from both directions, giving
    `f(c) ≤ 0` and `f(c) ≥ 0`, hence `f ≡ 0` on `[a,b]`.  Once
    the trajectory enters `(a,b)` it satisfies `y' = 0`, so it is
    constant, contradicting the existence of two distinct limit
    points.
-/
private lemma bounded_1d_ode_converges
    (f : ℝ → ℝ) (h_f_cont : Continuous f)
    (y : ℝ → ℝ) (hy : ∀ t : ℝ, HasDerivAt y (f (y t)) t)
    (hy_bdd : ∃ B : ℝ, ∀ t : ℝ, t ≥ 0 → |y t| ≤ B) :
    ∃ L : ℝ, Filter.Tendsto y Filter.atTop (nhds L) := by
  -- Assume y does not converge. Then there exist a and b in the ω-limit set of y with a < b.
  by_contra h_not_converge
  obtain ⟨a, b, hab⟩ : ∃ a b, a < b ∧ (∃ (t_n : ℕ → ℝ), Filter.Tendsto t_n Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun n => y (t_n n)) Filter.atTop (nhds a)) ∧ (∃ (s_n : ℕ → ℝ), Filter.Tendsto s_n Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun n => y (s_n n)) Filter.atTop (nhds b)) := by
    obtain ⟨a, ha⟩ : ∃ a, ∃ (t_n : ℕ → ℝ), Filter.Tendsto t_n Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun n => y (t_n n)) Filter.atTop (nhds a) := by
      have h_compact : IsCompact (Set.Icc (-hy_bdd.choose) hy_bdd.choose) := by
        exact CompactIccSpace.isCompact_Icc;
      have := h_compact.isSeqCompact fun n => show y ( n : ℝ ) ∈ Set.Icc ( -hy_bdd.choose ) hy_bdd.choose from ⟨ neg_le_of_abs_le <| hy_bdd.choose_spec _ <| Nat.cast_nonneg _, le_of_abs_le <| hy_bdd.choose_spec _ <| Nat.cast_nonneg _ ⟩;
      obtain ⟨ a, ha, φ, hφ₁, hφ₂ ⟩ := this; exact ⟨ a, fun n => φ n, tendsto_natCast_atTop_atTop.comp hφ₁.tendsto_atTop, hφ₂ ⟩ ;
    -- Since y does not converge to a, there exists an ε > 0 such that for all T, there exists t ≥ T with |y(t) - a| ≥ ε.
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ T, ∃ t ≥ T, |y t - a| ≥ ε := by
      exact not_forall_not.mp fun h => h_not_converge ⟨ a, Metric.tendsto_atTop.mpr fun ε hε => by push_neg at h; exact h ε hε ⟩;
    -- Choose a sequence $s_n$ such that $|y(s_n) - a| \geq \epsilon$ and $s_n \to \infty$.
    obtain ⟨s_n, hs_n⟩ : ∃ s_n : ℕ → ℝ, Filter.Tendsto s_n Filter.atTop Filter.atTop ∧ ∀ n, |y (s_n n) - a| ≥ ε := by
      exact ⟨ fun n => Classical.choose ( hε n ), Filter.tendsto_atTop_mono ( fun n => Classical.choose_spec ( hε n ) |>.1 ) tendsto_natCast_atTop_atTop, fun n => Classical.choose_spec ( hε n ) |>.2 ⟩;
    -- Since $y(s_n)$ is bounded, it has a convergent subsequence.
    obtain ⟨b, hb⟩ : ∃ b, ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧ Filter.Tendsto (fun n => y (s_n (subseq n))) Filter.atTop (nhds b) := by
      have h_bounded : ∃ B, ∀ n, |y (s_n n)| ≤ B := by
        obtain ⟨ B, hB ⟩ := hy_bdd;
        obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( hs_n.1.eventually_ge_atTop 0 );
        exact ⟨ Max.max B ( ∑ n ∈ Finset.range N, |y ( s_n n )| ), fun n => if hn : n < N then Finset.single_le_sum ( fun n _ => abs_nonneg ( y ( s_n n ) ) ) ( Finset.mem_range.mpr hn ) |> le_trans <| le_max_right _ _ else le_trans ( hB _ <| hN _ <| le_of_not_gt hn ) <| le_max_left _ _ ⟩;
      have h_compact : IsCompact (Set.Icc (-h_bounded.choose) h_bounded.choose) := by
        exact CompactIccSpace.isCompact_Icc;
      have := h_compact.isSeqCompact fun n => ⟨ neg_le_of_abs_le <| h_bounded.choose_spec n, le_of_abs_le <| h_bounded.choose_spec n ⟩ ; aesop;
    cases lt_trichotomy a b <;> simp_all +decide [ abs_eq_max_neg ];
    · exact ⟨ a, b, by linarith, ha, by obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hb; exact ⟨ fun n => s_n ( subseq n ), hs_n.1.comp hsubseq₁.tendsto_atTop, hsubseq₂ ⟩ ⟩;
    · cases' ‹_› with h h;
      · obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hb; have := hsubseq₂.eventually ( Metric.ball_mem_nhds _ hε_pos ) ; obtain ⟨ n, hn ⟩ := this.exists; cases hs_n.2 ( subseq n ) <;> linarith [ abs_lt.mp hn ] ;
      · exact ⟨ b, a, h, by obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hb; exact ⟨ fun n => s_n ( subseq n ), hs_n.1.comp hsubseq₁.tendsto_atTop, hsubseq₂ ⟩, by obtain ⟨ t_n, ht_n₁, ht_n₂ ⟩ := ha; exact ⟨ t_n, ht_n₁, ht_n₂ ⟩ ⟩;
  -- For any $c \in (a, b)$, $y$ crosses $c$ from both directions, giving $f(c) \leq 0$ and $f(c) \geq 0$, hence $f \equiv 0$ on $[a, b]$.
  have h_f_zero : ∀ c ∈ Set.Ioo a b, f c = 0 := by
    intros c hc
    have h_downcrossing : f c ≤ 0 := by
      -- Since $y$ does not converge, there exist sequences $t_n \to \infty$ and $s_n \to \infty$ such that $y(t_n) \to a$ and $y(s_n) \to b$.
      obtain ⟨t_n, ht_n⟩ := hab.right.left
      obtain ⟨s_n, hs_n⟩ := hab.right.right;
      -- Since $y$ does not converge, there exist sequences $t_n \to \infty$ and $s_n \to \infty$ such that $y(t_n) \to a$ and $y(s_n) \to b$. For large enough $n$, $y(t_n) < c$ and $y(s_n) > c$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, y (t_n n) < c ∧ y (s_n n) > c := by
        exact Filter.eventually_atTop.mp ( ht_n.2.eventually ( gt_mem_nhds hc.1 ) |> Filter.Eventually.and <| hs_n.2.eventually ( lt_mem_nhds hc.2 ) );
      -- Since $y$ does not converge, there exist sequences $t_n \to \infty$ and $s_n \to \infty$ such that $y(t_n) \to a$ and $y(s_n) \to b$. For large enough $n$, $y(t_n) < c$ and $y(s_n) > c$. Hence, $f(c) \leq 0$.
      have h_downcrossing : ∀ n ≥ N, ∃ t₁ t₂, t₁ < t₂ ∧ y t₁ > c ∧ y t₂ < c := by
        intros n hn
        obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₁ > s_n n ∧ y t₁ < c := by
          have := ht_n.2.eventually ( gt_mem_nhds hc.1 ) ; have := this.and ( ht_n.1.eventually_gt_atTop ( s_n n ) ) ; obtain ⟨ m, hm₁, hm₂ ⟩ := this.exists; exact ⟨ t_n m, hm₂, hm₁ ⟩ ;
        use s_n n, t₁
        aesop;
      exact f_nonpos_of_downcrossing f y c hy ( h_downcrossing N le_rfl |> Classical.choose_spec |> Classical.choose_spec |> And.left ) ( h_downcrossing N le_rfl |> Classical.choose_spec |> Classical.choose_spec |> And.right |> And.left ) ( h_downcrossing N le_rfl |> Classical.choose_spec |> Classical.choose_spec |> And.right |> And.right )
    have h_upcrossing : f c ≥ 0 := by
      -- By the properties of the ω-limit set, there exist sequences $t_n$ and $s_n$ such that $t_n \to \infty$, $s_n \to \infty$, $y(t_n) \to a$, and $y(s_n) \to b$.
      obtain ⟨t_n, ht_n⟩ := hab.right.left
      obtain ⟨s_n, hs_n⟩ := hab.right.right;
      -- Since $y(t_n) \to a$ and $y(s_n) \to b$, there exist $N$ and $M$ such that for all $n \geq N$, $y(t_n) < c$ and for all $n \geq M$, $y(s_n) > c$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, y (t_n n) < c := by
        exact Filter.eventually_atTop.mp ( ht_n.2.eventually ( gt_mem_nhds hc.1 ) )
      obtain ⟨M, hM⟩ : ∃ M, ∀ n ≥ M, y (s_n n) > c := by
        exact Filter.eventually_atTop.mp ( hs_n.2.eventually ( lt_mem_nhds hc.2 ) );
      -- Since $t_n \to \infty$ and $s_n \to \infty$, there exist $n \geq N$ and $m \geq M$ such that $t_n n < s_n m$.
      obtain ⟨n, hn⟩ : ∃ n ≥ N, ∃ m ≥ M, t_n n < s_n m := by
        have := hs_n.1.eventually_gt_atTop ( t_n N ) ; have := this.and ( Filter.eventually_ge_atTop M ) ; obtain ⟨ m, hm₁, hm₂ ⟩ := this.exists; exact ⟨ N, le_rfl, m, hm₂, hm₁ ⟩ ;
      obtain ⟨ m, hm₁, hm₂ ⟩ := hn.2; exact f_nonneg_of_upcrossing f y c hy hm₂ ( hN n hn.1 ) ( hM m hm₁ ) ;
    exact le_antisymm h_downcrossing h_upcrossing;
  -- Since $f \equiv 0$ on $[a, b]$, once the trajectory enters $(a, b)$ it satisfies $y' = 0$, so it is constant.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, y t₀ ∈ Set.Ioo a b := by
    rcases hab.2.1 with ⟨ t_n, ht_n₁, ht_n₂ ⟩ ; rcases hab.2.2 with ⟨ s_n, hs_n₁, hs_n₂ ⟩ ; have := ht_n₂.eventually ( gt_mem_nhds <| show a < ( a + b ) / 2 by linarith ) ; have := hs_n₂.eventually ( lt_mem_nhds <| show ( a + b ) / 2 < b by linarith ) ; simp_all +decide [ Metric.tendsto_nhds ] ;
    -- By the intermediate value theorem, since $y$ is continuous and $y(t_n) < (a + b) / 2$ and $y(s_n) > (a + b) / 2$, there exists some $t₀$ between $t_n$ and $s_n$ such that $y(t₀) = (a + b) / 2$.
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, y t₀ = (a + b) / 2 := by
      have h_ivt : IsConnected (Set.range y) := by
        exact isConnected_range ( show Continuous y from continuous_iff_continuousAt.mpr fun t => HasDerivAt.continuousAt ( hy t ) );
      exact h_ivt.Icc_subset ( Set.mem_range_self ( t_n ( Classical.choose ‹∃ a_1, ∀ b_1 : ℕ, a_1 ≤ b_1 → y ( t_n b_1 ) < ( a + b ) / 2› ) ) ) ( Set.mem_range_self ( s_n ( Classical.choose ‹∃ a_1, ∀ b_1 : ℕ, a_1 ≤ b_1 → ( a + b ) / 2 < y ( s_n b_1 ) › ) ) ) ⟨ by linarith [ Classical.choose_spec ‹∃ a_1, ∀ b_1 : ℕ, a_1 ≤ b_1 → y ( t_n b_1 ) < ( a + b ) / 2› ( Classical.choose ‹∃ a_1, ∀ b_1 : ℕ, a_1 ≤ b_1 → y ( t_n b_1 ) < ( a + b ) / 2› ) le_rfl ], by linarith [ Classical.choose_spec ‹∃ a_1, ∀ b_1 : ℕ, a_1 ≤ b_1 → ( a + b ) / 2 < y ( s_n b_1 ) › ( Classical.choose ‹∃ a_1, ∀ b_1 : ℕ, a_1 ≤ b_1 → ( a + b ) / 2 < y ( s_n b_1 ) › ) le_rfl ] ⟩;
    exact ⟨ t₀, by linarith, by linarith ⟩;
  -- Since $y$ is continuous and $y(t₀) \in (a, b)$, there exists an interval $(t₀ - ε, t₀ + ε)$ such that $y(t) \in (a, b)$ for all $t \in (t₀ - ε, t₀ + ε)$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ t, abs (t - t₀) < ε → y t ∈ Set.Ioo a b := by
    exact Metric.mem_nhds_iff.mp ( ContinuousAt.preimage_mem_nhds ( show ContinuousAt y t₀ from HasDerivAt.continuousAt ( hy t₀ ) ) ( Ioo_mem_nhds ht₀.1 ht₀.2 ) );
  -- Since $y$ is constant on $(t₀ - ε, t₀ + ε)$, we have $y(t) = y(t₀)$ for all $t \geq t₀$.
  have h_y_const_all : ∀ t, t₀ ≤ t → y t = y t₀ := by
    intro t ht;
    by_cases h_cases : ∀ t' ∈ Set.Icc t₀ t, y t' ∈ Set.Ioo a b;
    · have h_y_const_all : ∀ t', t₀ ≤ t' ∧ t' ≤ t → y t' = y t₀ := by
        intros t' ht'
        have h_deriv_zero : ∀ t'', t₀ ≤ t'' ∧ t'' ≤ t' → deriv y t'' = 0 := by
          exact fun t'' ht'' => HasDerivAt.deriv ( hy t'' ) ▸ h_f_zero _ ( h_cases t'' ⟨ by linarith, by linarith ⟩ ) ▸ rfl;
        by_cases h_cases : t' = t₀;
        · rw [h_cases];
        · have := exists_deriv_eq_slope y ( lt_of_le_of_ne ht'.1 ( Ne.symm h_cases ) );
          exact eq_of_sub_eq_zero ( by obtain ⟨ c, hc₁, hc₂ ⟩ := this ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy x ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( hy x |> HasDerivAt.differentiableAt ) ) ; rw [ h_deriv_zero c ⟨ by linarith [ hc₁.1 ], by linarith [ hc₁.2 ] ⟩ ] at hc₂; rw [ eq_div_iff ] at hc₂ <;> cases lt_or_gt_of_ne h_cases <;> linarith );
      exact h_y_const_all t ⟨ ht, le_rfl ⟩;
    · obtain ⟨t', ht', ht'_not⟩ : ∃ t' ∈ Set.Icc t₀ t, y t' ∉ Set.Ioo a b ∧ ∀ t'' ∈ Set.Ico t₀ t', y t'' ∈ Set.Ioo a b := by
        have h_inf : ∃ t' ∈ Set.Icc t₀ t, y t' ∉ Set.Ioo a b ∧ ∀ t'' ∈ Set.Ico t₀ t', y t'' ∈ Set.Ioo a b := by
          have h_nonempty : {t' ∈ Set.Icc t₀ t | y t' ∉ Set.Ioo a b}.Nonempty := by
            exact by push_neg at h_cases; exact h_cases;
          obtain ⟨t', ht'⟩ : ∃ t' ∈ {t' ∈ Set.Icc t₀ t | y t' ∉ Set.Ioo a b}, ∀ t'' ∈ {t' ∈ Set.Icc t₀ t | y t' ∉ Set.Ioo a b}, t' ≤ t'' := by
            apply_rules [ IsCompact.exists_isLeast, CompactIccSpace.isCompact_Icc ];
            exact CompactIccSpace.isCompact_Icc.of_isClosed_subset ( isClosed_Icc.inter <| isClosed_compl_iff.mpr <| isOpen_Ioo.preimage <| show Continuous y from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt <| hy x ) fun x hx => hx.1;
          exact ⟨ t', ht'.1.1, ht'.1.2, fun t'' ht'' => Classical.not_not.1 fun h => not_lt_of_ge ( ht'.2 t'' ⟨ ⟨ ht''.1, ht''.2.le.trans ht'.1.1.2 ⟩, h ⟩ ) ht''.2 ⟩;
        exact h_inf;
      -- Since $y$ is continuous and $y(t') \notin (a, b)$, we have $y(t') = a$ or $y(t') = b$.
      have h_y_t'_eq : y t' = a ∨ y t' = b := by
        have h_y_t'_eq : y t' ≤ b ∧ y t' ≥ a := by
          have h_y_t'_eq : Filter.Tendsto (fun t'' => y t'') (nhdsWithin t' (Set.Iio t')) (nhds (y t')) := by
            exact HasDerivAt.continuousAt ( hy t' ) |> ContinuousAt.continuousWithinAt;
          have h_y_t'_eq : ∀ᶠ t'' in nhdsWithin t' (Set.Iio t'), y t'' ∈ Set.Ioo a b := by
            filter_upwards [ Ioo_mem_nhdsLT ( show t' > t₀ from ht'.1.lt_of_ne ( by rintro rfl; exact ht'_not.1 ht₀ ) ) ] with t'' ht'' using ht'_not.2 t'' ⟨ by linarith [ ht''.1 ], by linarith [ ht''.2 ] ⟩;
          exact ⟨ le_of_tendsto_of_tendsto ‹_› tendsto_const_nhds ( Filter.eventually_of_mem h_y_t'_eq fun x hx => hx.2.le ), le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› ( Filter.eventually_of_mem h_y_t'_eq fun x hx => hx.1.le ) ⟩;
        grind;
      cases h_y_t'_eq <;> simp_all +decide [ Set.Ioo ];
      · have := exists_deriv_eq_slope y ( show t' > t₀ from ht'.1.lt_of_ne ( by rintro rfl; linarith [ hε t₀ ( by simpa ) ] ) ) ; simp_all +decide [ hy _ |> HasDerivAt.deriv ] ;
        exact absurd ( this ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy x ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( hy x |> HasDerivAt.differentiableAt ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; rw [ eq_div_iff ] at hc <;> nlinarith [ h_f_zero ( y c ) ( ht'_not c hc₁.le hc₂ |>.1 ) ( ht'_not c hc₁.le hc₂ |>.2 ), hε t₀ ( by simpa ) ] );
      · have := exists_deriv_eq_slope y ( show t' > t₀ from ht'.1.lt_of_ne ( by rintro rfl; linarith [ hε t₀ ( by simpa ) ] ) ) ; simp_all +decide [ hy _ |> HasDerivAt.deriv ] ;
        exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy x ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( hy x |> HasDerivAt.differentiableAt ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; rw [ h_f_zero _ ( ht'_not c hc₁.le hc₂ |>.1 ) ( ht'_not c hc₁.le hc₂ |>.2 ) ] at hc; rw [ eq_div_iff ] at hc <;> nlinarith [ hε t₀ ( by simpa ) ] );
  exact h_not_converge ⟨ y t₀, tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop t₀ ] with t ht; rw [ h_y_const_all t ht ] ) ⟩

/-
The limit of a convergent trajectory of `y' = f(y)` is a zero of `f`.
-/
private lemma limit_is_fixed_point
    (f : ℝ → ℝ) (h_f_cont : Continuous f)
    (y : ℝ → ℝ) (hy : ∀ t : ℝ, HasDerivAt y (f (y t)) t)
    {L : ℝ} (hL : Filter.Tendsto y Filter.atTop (nhds L)) :
    f L = 0 := by
  -- By the Mean Value Theorem, for any $t$, there exists $c_t \in (t, t+1)$ such that $y'(c_t) = \frac{y(t+1) - y(t)}{1}$.
  have h_mvt : ∀ t, ∃ c_t ∈ Set.Ioo t (t + 1), deriv y c_t = (y (t + 1) - y t) / 1 := by
    intro t;
    have := exists_deriv_eq_slope y ( by linarith : t < t + 1 );
    simpa using this ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy x ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( hy x |> HasDerivAt.differentiableAt ) );
  choose! c hc using h_mvt;
  -- Since $c_t \to \infty$ as $t \to \infty$, we have $f(y(c_t)) \to f(L)$.
  have h_f_y_ct : Filter.Tendsto (fun t => f (y (c t))) Filter.atTop (nhds (f L)) := by
    exact h_f_cont.continuousAt.tendsto.comp <| hL.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x, fun t ht => by linarith [ Set.mem_Ioo.mp <| hc t |>.1 ] ⟩;
  exact tendsto_nhds_unique h_f_y_ct ( by simpa using Filter.Tendsto.congr ( fun t => by have := hc t; have := hy ( c t ) ; have := this.deriv; aesop ) ( hL.comp ( show Filter.Tendsto ( fun t => t + 1 ) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_add tendsto_const_nhds ) |> Filter.Tendsto.sub <| hL ) )

/-
LaSalle's invariance principle: when the Lie derivative is
non-positive but possibly zero on a set `E`, trajectories from a
compact level set converge to the LARGEST invariant set contained
in `E`.

**Corrected statement**: the original scaffold was missing
`Continuous f`, `IsCompact Ω_c`, and a condition ensuring that all
equilibria of `f` in `Ω_c` lie in `M`. Without these, the statement
is false (e.g., `M = ∅` satisfies the original hypotheses vacuously
but the conclusion fails). The corrected version adds:
- `h_f_cont : Continuous f` for the convergence argument
- `h_compact : IsCompact Ω_c` to ensure bounded trajectories
- `h_fp_in_M : ∀ x ∈ Ω_c, f x = 0 → x ∈ M` so limit points land in `M`
-/
theorem lasalle_invariance
    (f : ℝ → ℝ) (h_zero : f 0 = 0)
    (h_f_cont : Continuous f)
    (V : ℝ → ℝ) (h_V_diff : ∀ y : ℝ, DifferentiableAt ℝ V y)
    (h_V_pos : ∀ y : ℝ, y ≠ 0 → 0 < V y)
    (h_lie : ∀ y : ℝ, deriv V y * f y ≤ 0)
    (c : ℝ) (h_c_pos : 0 < c)
    (Ω_c : Set ℝ) (h_Ω_c : Ω_c = {y | V y ≤ c})
    (h_compact : IsCompact Ω_c)
    (E : Set ℝ) (h_E : E = {y | deriv V y * f y = 0})
    (M : Set ℝ) (h_M : M ⊆ E)
    (h_M_invariant : ∀ y₀ ∈ M, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) → y 0 = y₀ →
      ∀ t : ℝ, y t ∈ M)
    (h_fp_in_M : ∀ x ∈ Ω_c, f x = 0 → x ∈ M) :
    ∀ y₀ ∈ Ω_c, ∀ (y : ℝ → ℝ),
      (∀ t : ℝ, HasDerivAt y (f (y t)) t) → y 0 = y₀ →
      ∃ y_inf ∈ M, Filter.Tendsto y Filter.atTop (nhds y_inf) := by
  intros y₀ hy₀ y hy hy₀_eq
  have h_bounded : ∃ B, ∀ t ≥ 0, |y t| ≤ B := by
    have h_bounded : ∀ t ≥ 0, y t ∈ Ω_c := by
      intro t ht
      have h_V_le_c : V (y t) ≤ V (y 0) := by
        have := V_comp_y_antitone f V y h_V_diff h_lie hy;
        exact this ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ht;
      grind;
    exact h_compact.isBounded.exists_norm_le.imp fun B hB t ht => hB _ ( h_bounded t ht );
  obtain ⟨ L, hL ⟩ := bounded_1d_ode_converges f h_f_cont y hy h_bounded;
  -- By the properties of the derivative and the intermediate value theorem, we know that $f(L) = 0$.
  have h_fL : f L = 0 := by
    exact?;
  refine' ⟨ L, h_fp_in_M L _ h_fL, hL ⟩;
  have hL_in_Ω_c : ∀ t ≥ 0, y t ∈ Ω_c := by
    intros t ht
    have h_V_le_c : V (y t) ≤ V (y 0) := by
      have h_V_le_c : AntitoneOn (V ∘ y) (Set.Ici 0) := by
        apply_rules [ V_comp_y_antitone ];
      exact h_V_le_c ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ht;
    grind;
  exact h_compact.isClosed.mem_of_tendsto hL ( Filter.eventually_atTop.mpr ⟨ 0, hL_in_Ω_c ⟩ )

end Pythia.Numerical.Lyapunov