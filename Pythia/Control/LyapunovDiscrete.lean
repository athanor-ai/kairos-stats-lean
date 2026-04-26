/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lyapunov direct method – discrete-time version

Reference: Khalil, *Nonlinear Systems*, 4th ed., Theorem 4.1 (discrete-time analogue).

We prove that a discrete-time system  `x_{n+1} = f(x_n)` with `f(0) = 0`
is **asymptotically stable** at the origin whenever there exists a Lyapunov
function `V` that is

* continuous on `closedBall 0 r`,
* zero at the origin,
* positive-definite (`V x > 0` for `x ≠ 0`), and
* strictly decreasing along non-trivial orbits (`V(f x) < V x` for `x ≠ 0`),

all within a closed ball of radius `r > 0` that is mapped into itself by `f`.

**Asymptotic stability** means:

1. **Stability** – `∀ ε > 0, ∃ δ > 0` such that `‖x₀‖ < δ` implies
   `‖f^[n] x₀‖ < ε` for every `n`.
2. **Attractivity** – `∃ δ > 0` such that `‖x₀‖ < δ` implies
   `f^[n] x₀ → 0`.

The space `E` is any real normed space that is *proper* (closed balls are
compact), which covers `ℝⁿ = EuclideanSpace ℝ (Fin d)`.
-/
import Mathlib

namespace Pythia.Control.LyapunovDiscrete

open Metric Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-! ## Helper lemmas -/

/-
The orbit `f^[n] x₀` stays inside a closed ball that is `f`-invariant.
-/
lemma orbit_mem_closedBall {f : E → E} {r : ℝ} {x₀ : E}
    (hf : ∀ x ∈ closedBall (0 : E) r, f x ∈ closedBall (0 : E) r)
    (hx₀ : x₀ ∈ closedBall (0 : E) r) :
    ∀ n, f^[n] x₀ ∈ closedBall (0 : E) r := by
      exact fun n => Nat.recOn n hx₀ fun n ih => by simpa only [ Function.iterate_succ_apply' ] using hf _ ih;

/-
`V` is non-negative along every orbit inside the invariant ball.
-/
lemma V_nonneg_along_orbit {f : E → E} {V : E → ℝ} {r : ℝ} {x₀ : E}
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hfball : ∀ x ∈ closedBall (0 : E) r, f x ∈ closedBall (0 : E) r)
    (hx₀ : x₀ ∈ closedBall (0 : E) r) :
    ∀ n, 0 ≤ V (f^[n] x₀) := by
      intro n;
      by_cases h : f^[n] x₀ = 0;
      · rw [ h, hV0 ];
      · exact le_of_lt ( hVpos _ ( by exact Nat.recOn n hx₀ fun n ihn => by simpa only [ Function.iterate_succ_apply' ] using hfball _ ihn ) h )

/-
`V` is weakly decreasing along every orbit inside the invariant ball.
-/
lemma V_antitone_along_orbit {f : E → E} {V : E → ℝ} {r : ℝ} {x₀ : E}
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdec : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → V (f x) < V x)
    (hfball : ∀ x ∈ closedBall (0 : E) r, f x ∈ closedBall (0 : E) r)
    (hx₀ : x₀ ∈ closedBall (0 : E) r) :
    Antitone (fun n => V (f^[n] x₀)) := by
      refine' antitone_nat_of_succ_le _;
      intro n;
      by_cases h : f^[n] x₀ = 0 <;> simp +decide [ *, Function.iterate_succ_apply' ];
      exact le_of_lt ( hVdec _ ( orbit_mem_closedBall hfball hx₀ n ) h )

/-
On the compact annulus `{ε ≤ ‖x‖} ∩ closedBall 0 r`, the continuous
positive-definite function `V` has a strictly positive lower bound.
-/
lemma V_pos_lower_bound_annulus {V : E → ℝ} {r ε : ℝ}
    (_hr : 0 < r) (hε : 0 < ε) (_hεr : ε ≤ r)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x) :
    ∃ β > 0, ∀ x ∈ closedBall (0 : E) r, ε ≤ ‖x‖ → β ≤ V x := by
      by_contra! h_contra;
      -- Since $V$ is continuous on the compact set $S$, it attains its minimum value $m$ on $S$.
      obtain ⟨m, hm⟩ : ∃ m ∈ (Set.image V {x ∈ closedBall (0 : E) r | ε ≤ ‖x‖}), ∀ y ∈ (Set.image V {x ∈ closedBall (0 : E) r | ε ≤ ‖x‖}), m ≤ y := by
        apply_rules [ IsCompact.exists_isLeast, IsCompact.image_of_continuousOn ];
        · exact ( ProperSpace.isCompact_closedBall _ _ ).of_isClosed_subset ( isClosed_closedBall.inter ( isClosed_le continuous_const continuous_norm ) ) fun x hx => hx.1;
        · exact hVcont.mono fun x hx => hx.1;
        · exact Exists.elim ( h_contra 1 zero_lt_one ) fun x hx => ⟨ V x, Set.mem_image_of_mem _ ⟨ hx.1, hx.2.1 ⟩ ⟩;
      obtain ⟨ ⟨ x, hx, rfl ⟩, hm ⟩ := hm;
      exact absurd ( h_contra ( V x ) ( hVpos x hx.1 ( by rintro rfl; norm_num at hx; linarith ) ) ) ( by rintro ⟨ y, hy, hy', hy'' ⟩ ; linarith [ hm _ ⟨ y, ⟨ hy, hy' ⟩, rfl ⟩ ] )

/-! ## Part 1 – Lyapunov stability -/

/-
**Lyapunov stability (discrete-time).**
Given `ε > 0` there exists `δ > 0` such that every orbit starting in
`ball 0 δ` remains in `ball 0 ε` for all time.
-/
theorem lyapunov_stability {f : E → E} {V : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdec : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → V (f x) < V x)
    (hfball : ∀ x ∈ closedBall (0 : E) r, f x ∈ closedBall (0 : E) r) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₀, ‖x₀‖ < δ → ∀ n, ‖f^[n] x₀‖ < ε := by
      intro ε hε
      obtain ⟨β, hβ_pos, hβ⟩ : ∃ β > 0, ∀ x ∈ closedBall 0 r, min ε r ≤ ‖x‖ → β ≤ V x := by
        apply V_pos_lower_bound_annulus hr (lt_min hε hr) (min_le_right ε r) hVcont hVpos;
      -- By continuity of $V$ at $0$, there exists $\delta_1 > 0$ such that if $\|x\| < \delta_1$, then $V(x) < \beta$.
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x, ‖x‖ < δ₁ → V x < β := by
        have := Metric.continuousOn_iff.mp hVcont 0 ( by simp +decide [ hr.le ] ) β hβ_pos;
        obtain ⟨ δ₁, hδ₁_pos, H ⟩ := this; exact ⟨ Min.min δ₁ r, lt_min hδ₁_pos hr, fun x hx => by linarith [ abs_lt.mp ( H x ( by simpa using hx.le.trans ( min_le_right _ _ ) ) ( by simpa using hx.trans_le ( min_le_left _ _ ) ) ) ] ⟩ ;
      refine' ⟨ Min.min δ₁ ( Min.min ε r ), lt_min hδ₁_pos ( lt_min hε hr ), fun x₀ hx₀ n => _ ⟩;
      -- By induction on $n$, we show that $V(f^[n] x₀) < β$ for all $n$.
      have h_ind : ∀ n, V (f^[n] x₀) < β := by
        intro n
        induction' n with n ih;
        · exact hδ₁ x₀ ( lt_of_lt_of_le hx₀ ( min_le_left _ _ ) );
        · by_cases h : f^[n] x₀ = 0 <;> simp_all +decide [Function.iterate_succ_apply'];
          exact lt_of_lt_of_le ( hVdec _ ( by exact Nat.recOn n ( by simpa using hx₀.2.2.le ) fun n ihn => by simpa only [ Function.iterate_succ_apply' ] using hfball _ ihn ) h ) ih.le;
      contrapose! hβ;
      refine' ⟨ f^[n] x₀, _, _, h_ind n ⟩ <;> simp_all +decide [ Function.iterate_succ_apply' ];
      exact Nat.recOn n ( by simpa using hx₀.2.2.le ) fun n ihn => by simpa only [ Function.iterate_succ_apply' ] using hfball _ ihn;

/-! ## Part 2 – Attractivity -/

/-
`V` converges to zero along every orbit starting in the invariant ball.
-/
lemma V_tendsto_zero {f : E → E} {V : E → ℝ} {r : ℝ} (hr : 0 < r)
    {x₀ : E}
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hfcont : ContinuousOn f (closedBall 0 r))
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdec : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → V (f x) < V x)
    (hfball : ∀ x ∈ closedBall (0 : E) r, f x ∈ closedBall (0 : E) r)
    (hx₀ : x₀ ∈ closedBall (0 : E) r) :
    Tendsto (fun n => V (f^[n] x₀)) atTop (nhds 0) := by
      -- By contradiction, assume $c > 0$.
      by_contra h_contra
      obtain ⟨c, hc⟩ : ∃ c, Filter.Tendsto (fun n => V (f^[n] x₀)) Filter.atTop (nhds c) ∧ c > 0 := by
        have h_lim_pos : ∃ c, Filter.Tendsto (fun n => V (f^[n] x₀)) Filter.atTop (nhds c) := by
          have h_antitone : Antitone (fun n => V (f^[n] x₀)) := by
            apply_rules [ V_antitone_along_orbit ];
          exact ⟨ _, tendsto_atTop_ciInf h_antitone ⟨ 0, Set.forall_mem_range.2 fun n => V_nonneg_along_orbit hf0 hV0 hVpos hfball hx₀ n ⟩ ⟩;
        exact h_lim_pos.imp fun c hc => ⟨ hc, lt_of_le_of_ne ( le_of_tendsto_of_tendsto' tendsto_const_nhds hc fun n => by exact ( show 0 ≤ V ( f^[n] x₀ ) from le_of_not_gt fun h => by have := hVpos ( f^[n] x₀ ) ( by exact orbit_mem_closedBall hfball hx₀ n ) ( by aesop ) ; linarith ) ) ( Ne.symm <| by aesop ) ⟩;
      -- Since $c > 0$, there exists a subsequence $f^{n_k}(x_0)$ converging to some $x^* \in \overline{B}(0, r)$.
      obtain ⟨x_star, hx_star⟩ : ∃ x_star ∈ Metric.closedBall 0 r, ∃ (nk : ℕ → ℕ), StrictMono nk ∧ Filter.Tendsto (fun k => f^[nk k] x₀) Filter.atTop (nhds x_star) ∧ V x_star = c := by
        -- Since $c > 0$, there exists a subsequence $f^{n_k}(x_0)$ converging to some $x^* \in \overline{B}(0, r)$ by the Bolzano-Weierstrass theorem.
        obtain ⟨x_star, hx_star⟩ : ∃ x_star ∈ Metric.closedBall 0 r, ∃ (nk : ℕ → ℕ), StrictMono nk ∧ Filter.Tendsto (fun k => f^[nk k] x₀) Filter.atTop (nhds x_star) := by
          have h_compact : IsCompact (Metric.closedBall (0 : E) r) := by
            exact ProperSpace.isCompact_closedBall _ _;
          exact h_compact.isSeqCompact fun n => orbit_mem_closedBall hfball hx₀ n;
        refine' ⟨ x_star, hx_star.1, hx_star.2.choose, hx_star.2.choose_spec.1, hx_star.2.choose_spec.2, _ ⟩;
        refine' tendsto_nhds_unique _ ( hc.1.comp hx_star.2.choose_spec.1.tendsto_atTop );
        exact hVcont.continuousWithinAt ( show x_star ∈ closedBall 0 r from hx_star.1 ) |> fun h => h.tendsto.comp ( Filter.tendsto_inf.2 ⟨ hx_star.2.choose_spec.2, Filter.tendsto_principal.2 <| Filter.Eventually.of_forall fun n => show f^[hx_star.2.choose n] x₀ ∈ closedBall 0 r from by exact Nat.recOn ( hx_star.2.choose n ) hx₀ fun n ihn => by simpa only [ Function.iterate_succ_apply' ] using hfball _ ihn ⟩ );
      -- Since $x^* \neq 0$, we have $V(f(x^*)) < V(x^*)$.
      have hV_fx_star : V (f x_star) < V x_star := by
        grind +splitImp;
      -- Since $f^{n_k}(x_0) \to x^*$, we have $f^{n_k+1}(x_0) \to f(x^*)$.
      obtain ⟨nk, hnk_mono, hnk_conv, hnk_eq⟩ := hx_star.right;
      have hnk_succ_conv : Filter.Tendsto (fun k => f^[nk k + 1] x₀) Filter.atTop (nhds (f x_star)) := by
        simpa only [ Function.iterate_succ_apply' ] using hfcont.continuousWithinAt ( show x_star ∈ closedBall 0 r from hx_star.1 ) |> fun h => h.tendsto.comp ( Filter.tendsto_inf.2 ⟨ hnk_conv, Filter.tendsto_principal.2 <| Filter.Eventually.of_forall fun k => by exact Nat.recOn ( nk k ) ( by simpa using hx₀ ) fun n ihn => by simpa only [ Function.iterate_succ_apply' ] using hfball _ ihn ⟩ );
      -- Since $V$ is continuous on the closed ball, we have $V(f^{n_k+1}(x_0)) \to V(f(x^*))$.
      have hnk_succ_V_conv : Filter.Tendsto (fun k => V (f^[nk k + 1] x₀)) Filter.atTop (nhds (V (f x_star))) := by
        apply Filter.Tendsto.comp;
        apply_rules [ ContinuousOn.continuousAt ];
        · exact hx_star.1;
        · rw [ tendsto_nhdsWithin_iff ];
          exact ⟨ hnk_succ_conv, Filter.Eventually.of_forall fun n => by simpa only [ Function.iterate_succ_apply' ] using hfball _ ( orbit_mem_closedBall hfball hx₀ _ ) ⟩;
      exact absurd ( tendsto_nhds_unique hnk_succ_V_conv ( hc.1.comp ( Filter.tendsto_add_atTop_nat 1 |> Filter.Tendsto.comp <| hnk_mono.tendsto_atTop ) ) ) ( by linarith )

/-
**Attractivity (discrete-time).**
There exists `δ > 0` such that every orbit starting in `ball 0 δ`
converges to the origin.
-/
theorem lyapunov_attractivity {f : E → E} {V : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hfcont : ContinuousOn f (closedBall 0 r))
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdec : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → V (f x) < V x)
    (hfball : ∀ x ∈ closedBall (0 : E) r, f x ∈ closedBall (0 : E) r) :
    ∃ δ > 0, ∀ x₀, ‖x₀‖ < δ →
      Tendsto (fun n => f^[n] x₀) atTop (nhds 0) := by
        use r, hr;
        intro x₀ hx₀
        have h_orbit : ∀ n, f^[n] x₀ ∈ closedBall (0 : E) r := by
          exact fun n => Nat.recOn n ( by simpa using hx₀.le ) fun n ih => by simpa only [ Function.iterate_succ_apply' ] using hfball _ ih;
        have h_V_zero : Filter.Tendsto (fun n => V (f^[n] x₀)) Filter.atTop (nhds 0) := by
          convert V_tendsto_zero hr hf0 hV0 hfcont hVcont hVpos hVdec hfball ( by simpa using hx₀.le ) using 1;
        -- To show f^[n] x₀ → 0, use the characterization via Metric.tendsto_atTop: ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖f^[n] x₀‖ < ε.
        have h_converge : ∀ ε > 0, ε ≤ r → ∃ N, ∀ n ≥ N, ‖f^[n] x₀‖ < ε := by
          intro ε hε_pos hε_le_r
          obtain ⟨β, hβ_pos, hβ⟩ : ∃ β > 0, ∀ x ∈ closedBall (0 : E) r, ε ≤ ‖x‖ → β ≤ V x := by
            apply_rules [ V_pos_lower_bound_annulus ];
          exact Filter.eventually_atTop.mp ( h_V_zero.eventually ( gt_mem_nhds hβ_pos ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn ↦ not_le.mp fun h ↦ not_lt_of_ge ( hβ _ ( h_orbit n ) h ) ( hN n hn ) ⟩;
        exact Metric.tendsto_atTop.mpr fun ε εpos => by rcases h_converge ( Min.min ε r ) ( lt_min εpos hr ) ( min_le_right _ _ ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => by simpa [ dist_eq_norm ] using lt_of_lt_of_le ( hN n hn ) ( min_le_left _ _ ) ⟩ ;

/-! ## Main theorem – Asymptotic stability -/

/-
**Lyapunov asymptotic stability (discrete-time, Khalil Thm 4.1).**
Combines stability and attractivity into a single statement.
-/
theorem lyapunov_asymptotic_stability
    {f : E → E} {V : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hfcont : ContinuousOn f (closedBall 0 r))
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdec : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → V (f x) < V x)
    (hfball : ∀ x ∈ closedBall (0 : E) r, f x ∈ closedBall (0 : E) r) :
    (∀ ε > 0, ∃ δ > 0, ∀ x₀, ‖x₀‖ < δ → ∀ n, ‖f^[n] x₀‖ < ε) ∧
    (∃ δ > 0, ∀ x₀, ‖x₀‖ < δ →
      Tendsto (fun n => f^[n] x₀) atTop (nhds 0)) := by
        exact ⟨ lyapunov_stability hr hf0 hV0 hVcont hVpos hVdec hfball, lyapunov_attractivity hr hf0 hV0 hfcont hVcont hVpos hVdec hfball ⟩

end Pythia.Control.LyapunovDiscrete