/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lyapunov direct method – continuous-time ODE version

Reference: Khalil, *Nonlinear Systems*, 4th ed., Theorem 4.1; Lyapunov (1892).

We prove that a continuous-time autonomous ODE  ẋ = f(x) with f(0) = 0
is **asymptotically stable** at the origin whenever there exists a
Lyapunov function V satisfying

* V(0) = 0,
* V(x) > 0 for x ≠ 0 (in a neighborhood of the origin),
* the **orbital derivative** V̇(x) := DV(x)(f(x)) < 0 for x ≠ 0.

**Asymptotic stability** means:

1. **Stability** – ∀ ε > 0, ∃ δ > 0 such that ‖x₀‖ < δ implies
   ‖Φ(x₀, t)‖ < ε for every t ≥ 0.
2. **Attractivity** – ∃ δ > 0 such that ‖x₀‖ < δ implies
   Φ(x₀, t) → 0 as t → +∞.

## Proof strategy

1. **Chain rule** connects d/dt V(φ(t)) to the orbital derivative V̇(φ(t)).
2. **Monotonicity**: V(φ(t)) is non-increasing, giving stability via
   sublevel-set containment.
3. **Decay to zero**: If V(φ(t)) → c > 0, compactness of the sublevel set
   {V ≥ c} ∩ B̄(0,r) yields a uniform upper bound V̇ ≤ d < 0 there, so
   V(φ(t)) ≤ V(φ(0)) + d·t → −∞, contradicting V ≥ 0.
4. **Attractivity**: V → 0 plus positive-definiteness lower bounds on
   annuli force φ(t) → 0.

## Setup

We abstract the ODE solution as a *flow map* Φ : E → ℝ → E satisfying the
ODE pointwise, avoiding the need to re-derive Picard–Lindelöf.  The space E
is any real normed space that is *proper* (closed balls are compact), which
covers ℝⁿ = EuclideanSpace ℝ (Fin d).
-/
import Mathlib

namespace Pythia.Control.LyapunovODE

open Metric Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-! ## Orbital derivative -/

/-- The **orbital derivative** (Lie derivative) of a scalar function `V` along
the vector field `f`, defined as `V̇(x) = DV(x)(f(x))`.  When `E` is an
inner-product space this equals `⟨∇V(x), f(x)⟩`. -/
noncomputable def orbitalDeriv (V : E → ℝ) (f : E → E) (x : E) : ℝ :=
  fderiv ℝ V x (f x)

/-! ## Chain rule -/

/-
**Chain rule for Lyapunov functions along ODE trajectories.**
If `φ'(t) = f(φ(t))` and `V` is differentiable at `φ(t)`, then
`(V ∘ φ)'(t) = orbitalDeriv V f (φ(t))`.
-/
theorem hasDerivAt_lyapunov_comp {V : E → ℝ} {f : E → E} {φ : ℝ → E} {t : ℝ}
    (hφ : HasDerivAt φ (f (φ t)) t)
    (hV : DifferentiableAt ℝ V (φ t)) :
    HasDerivAt (V ∘ φ) (orbitalDeriv V f (φ t)) t := by
  simpa using hV.hasFDerivAt.comp_hasDerivAt _ hφ

/-
The orbital derivative at the equilibrium is zero.
-/
lemma orbitalDeriv_eq_zero (V : E → ℝ) (f : E → E) (hf0 : f 0 = 0) :
    orbitalDeriv V f 0 = 0 := by
  unfold orbitalDeriv; aesop;

/-
The orbital derivative is non-positive on the invariant ball.
-/
lemma orbitalDeriv_nonpos {V : E → ℝ} {f : E → E} {r : ℝ}
    (hf0 : f 0 = 0)
    (hVdot : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → orbitalDeriv V f x < 0)
    {x : E} (hx : x ∈ closedBall (0 : E) r) :
    orbitalDeriv V f x ≤ 0 := by
  by_cases hx0 : x = 0 <;> simp_all +decide [ orbitalDeriv_eq_zero ];
  exact le_of_lt ( hVdot x hx hx0 )

/-! ## Monotonicity of V along trajectories -/

/-
`V ∘ φ` is antitone (non-increasing) on `[0, ∞)` when the orbital
derivative is non-positive and `φ` satisfies the ODE.
-/
lemma V_antitoneOn_trajectory {V : E → ℝ} {f : E → E} {φ : ℝ → E} {r : ℝ}
    (hf0 : f 0 = 0)
    (hVdiff : ∀ x ∈ closedBall (0 : E) r, DifferentiableAt ℝ V x)
    (hVdot : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → orbitalDeriv V f x < 0)
    (hφode : ∀ t, 0 ≤ t → HasDerivAt φ (f (φ t)) t)
    (hφball : ∀ t, 0 ≤ t → φ t ∈ closedBall (0 : E) r) :
    AntitoneOn (V ∘ φ) (Set.Ici 0) := by
  -- The function g = V ∘ φ is differentiable on [0, ∞) (by chain rule: hasDerivAt_lyapunov_comp gives HasDerivAt at each point).
  have h_diff : ∀ t, 0 ≤ t → DifferentiableAt ℝ (V ∘ φ) t := by
    exact fun t ht => DifferentiableAt.comp t ( hVdiff _ ( hφball t ht ) ) ( hφode t ht |> HasDerivAt.differentiableAt );
  apply_rules [ antitoneOn_of_deriv_nonpos ];
  · exact convex_Ici _;
  · exact fun t ht => DifferentiableAt.continuousAt ( h_diff t ht ) |> ContinuousAt.continuousWithinAt;
  · exact fun t ht => DifferentiableAt.differentiableWithinAt ( h_diff t ( interior_subset ht ) );
  · intro t ht;
    rw [ hasDerivAt_lyapunov_comp ( hφode t ( interior_subset ht ) ) ( hVdiff _ ( hφball t ( interior_subset ht ) ) ) |> HasDerivAt.deriv ];
    exact orbitalDeriv_nonpos hf0 hVdot ( hφball t ( interior_subset ht ) )

/-
`V` is non-negative along trajectories in the invariant ball.
-/
lemma V_nonneg_along_trajectory {V : E → ℝ} {φ : ℝ → E} {r : ℝ}
    (hV0 : V 0 = 0)
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hφball : ∀ t, 0 ≤ t → φ t ∈ closedBall (0 : E) r)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ V (φ t) := by
  grind +splitImp

/-! ## Positive lower bound on annular regions -/

/-
On the compact annulus `{ε ≤ ‖x‖} ∩ closedBall 0 r`, a continuous
positive-definite function `V` has a strictly positive lower bound.
-/
lemma V_pos_lower_bound_annulus {V : E → ℝ} {r ε : ℝ}
    (_hr : 0 < r) (hε : 0 < ε) (_hεr : ε ≤ r)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x) :
    ∃ β > 0, ∀ x ∈ closedBall (0 : E) r, ε ≤ ‖x‖ → β ≤ V x := by
  -- The set S = {x ∈ closedBall 0 r | ε ≤ ‖x‖} is compact (closed subset of a compact set in a proper space).
  have h_compact : IsCompact {x ∈ closedBall (0 : E) r | ε ≤ ‖x‖} := by
    exact ( ProperSpace.isCompact_closedBall 0 r ) |> fun h => h.of_isClosed_subset ( isClosed_closedBall.inter <| isClosed_le continuous_const <| continuous_norm ) fun x hx => hx.1;
  by_cases h_empty : {x ∈ closedBall (0 : E) r | ε ≤ ‖x‖} = ∅;
  · exact ⟨ 1, zero_lt_one, fun x hx hx' => False.elim <| h_empty.subset ⟨ hx, hx' ⟩ ⟩;
  · obtain ⟨ β, hβ ⟩ := h_compact.exists_isMinOn ( Set.nonempty_iff_ne_empty.2 h_empty ) ( show ContinuousOn V { x : E | x ∈ closedBall 0 r ∧ ε ≤ ‖x‖ } from hVcont.mono fun x hx => hx.1 );
    exact ⟨ V β, hVpos β hβ.1.1 ( by rintro rfl; norm_num at hβ; linarith ), fun x hx hx' => hβ.2 ⟨ hx, hx' ⟩ ⟩

/-! ## Decay of V to zero -/

/-
On a compact set where `V̇` is continuous and strictly negative, `V̇` is
bounded above by some `d < 0`.
-/
lemma orbitalDeriv_neg_bound {V : E → ℝ} {f : E → E} {r c : ℝ}
    (_hr : 0 < r) (hc : 0 < c)
    (hV0 : V 0 = 0)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVdotCont : ContinuousOn (orbitalDeriv V f) (closedBall 0 r))
    (hVdot : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → orbitalDeriv V f x < 0) :
    ∃ d < (0 : ℝ), ∀ x ∈ closedBall (0 : E) r, c ≤ V x →
      orbitalDeriv V f x ≤ d := by
  by_cases h_empty : {x ∈ closedBall 0 r | c ≤ V x} = ∅;
  · exact ⟨ -1, by norm_num, fun x hx hx' => False.elim <| h_empty.subset ⟨ hx, hx' ⟩ ⟩;
  · -- Since $K$ is nonempty and compact, and $V$ is continuous on $K$, $V$ attains a maximum value $d$ on $K$.
    obtain ⟨d, hd⟩ : ∃ d ∈ Set.image (orbitalDeriv V f) ({x ∈ closedBall 0 r | c ≤ V x}), ∀ y ∈ Set.image (orbitalDeriv V f) ({x ∈ closedBall 0 r | c ≤ V x}), y ≤ d := by
      apply_rules [ IsCompact.exists_isGreatest, IsCompact.image_of_continuousOn ];
      · exact IsCompact.of_isClosed_subset ( ProperSpace.isCompact_closedBall _ _ ) ( hVcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Ici ) fun x hx => hx.1;
      · exact hVdotCont.mono fun x hx => hx.1;
      · exact Set.nonempty_iff_ne_empty.2 h_empty |> fun ⟨ x, hx ⟩ => ⟨ _, ⟨ x, hx, rfl ⟩ ⟩;
    exact ⟨ d, by rcases hd.1 with ⟨ x, hx, rfl ⟩ ; exact hVdot x hx.1 ( by rintro rfl; linarith [ hx.2 ] ), fun x hx hx' => hd.2 _ ⟨ x, ⟨ hx, hx' ⟩, rfl ⟩ ⟩

/-
**Linear decay bound**: if `(V ∘ φ)'(t) ≤ d` for all `t` in `[0, T]`,
then `V(φ(T)) ≤ V(φ(0)) + d · T`.
-/
lemma V_linear_decay {V : E → ℝ} {f : E → E} {φ : ℝ → E} {r d : ℝ}
    (hVdiff : ∀ x ∈ closedBall (0 : E) r, DifferentiableAt ℝ V x)
    (hφode : ∀ t, 0 ≤ t → HasDerivAt φ (f (φ t)) t)
    (hφball : ∀ t, 0 ≤ t → φ t ∈ closedBall (0 : E) r)
    (hbound : ∀ t, 0 ≤ t → orbitalDeriv V f (φ t) ≤ d)
    {T : ℝ} (hT : 0 ≤ T) :
    (V ∘ φ) T ≤ (V ∘ φ) 0 + d * T := by
  by_contra h;
  -- Apply the mean value theorem to the interval $[0, T]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 T, deriv (V ∘ φ) c = (V (φ T) - V (φ 0)) / (T - 0) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hT.lt_of_ne ( by rintro rfl; norm_num at h );
    · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.comp ( hVdiff _ ( hφball t ht.1 ) |> DifferentiableAt.continuousAt ) ( hφode t ht.1 |> HasDerivAt.continuousAt );
    · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.comp t ( hVdiff _ ( hφball _ ht.1.le ) ) ( hφode _ ht.1.le |> HasDerivAt.differentiableAt ) );
  -- By the chain rule, we have `deriv (V ∘ φ) c = orbitalDeriv V f (φ c)`.
  have h_chain : deriv (V ∘ φ) c = orbitalDeriv V f (φ c) := by
    exact HasDerivAt.deriv ( hasDerivAt_lyapunov_comp ( hφode c hc.1.1.le ) ( hVdiff _ ( hφball c hc.1.1.le ) ) );
  rw [ eq_div_iff ] at hc <;> nlinarith! [ hc.1.1, hc.1.2, hbound c hc.1.1.le ]

/-
**V converges to zero** along any trajectory that remains in the
invariant ball.  Key step: if the limit were `c > 0`, the orbit would stay
in the compact set `{V ≥ c}` where `V̇ ≤ d < 0`, yielding the impossible
bound `V(φ(t)) ≤ V(φ(0)) + d·t → −∞`.
-/
theorem V_tendsto_zero_ode {V : E → ℝ} {f : E → E} {φ : ℝ → E} {r : ℝ}
    (hr : 0 < r)
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVdiff : ∀ x ∈ closedBall (0 : E) r, DifferentiableAt ℝ V x)
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdot : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → orbitalDeriv V f x < 0)
    (hVdotCont : ContinuousOn (orbitalDeriv V f) (closedBall 0 r))
    (hφode : ∀ t, 0 ≤ t → HasDerivAt φ (f (φ t)) t)
    (hφball : ∀ t, 0 ≤ t → φ t ∈ closedBall (0 : E) r) :
    Tendsto (V ∘ φ) atTop (nhds 0) := by
  -- By contradiction, assume $c > 0$.
  by_contra h_contra;
  -- Assume that the limit $c$ exists and is positive.
  obtain ⟨c, hc⟩ : ∃ c, Filter.Tendsto (V ∘ φ) Filter.atTop (nhds c) ∧ 0 < c := by
    have h_lim : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds (sInf {V (φ t) | t ≥ 0})) := by
      have h_antitone : AntitoneOn (V ∘ φ) (Set.Ici 0) := by
        apply_rules [ V_antitoneOn_trajectory ];
      refine' ( tendsto_order.2 ⟨ fun x hx => _, fun x hx => _ ⟩ );
      · exact Filter.eventually_atTop.2 ⟨ 0, fun t ht => hx.trans_le <| csInf_le ⟨ 0, by rintro _ ⟨ u, hu, rfl ⟩ ; exact V_nonneg_along_trajectory hV0 hVpos hφball hu ⟩ ⟨ t, ht, rfl ⟩ ⟩;
      · rcases exists_lt_of_csInf_lt ( by exact ⟨ _, ⟨ 0, le_rfl, rfl ⟩ ⟩ ) hx with ⟨ y, ⟨ t, ht, rfl ⟩, hy ⟩ ; filter_upwards [ Filter.eventually_ge_atTop t ] with u hu using lt_of_le_of_lt ( h_antitone ( show 0 ≤ t by linarith ) ( show 0 ≤ u by linarith ) hu ) hy;
    refine' ⟨ _, h_lim, lt_of_le_of_ne _ ( Ne.symm _ ) ⟩;
    · exact le_csInf ⟨ _, ⟨ 0, le_rfl, rfl ⟩ ⟩ fun x hx => by rcases hx with ⟨ t, ht, rfl ⟩ ; exact V_nonneg_along_trajectory hV0 hVpos hφball ht;
    · exact fun h => h_contra <| h_lim.trans <| by simp +decide [ h ] ;
  -- By the properties of the orbital derivative, there exists $d < 0$ such that $orbitalDeriv V f (φ t) ≤ d$ for all $t ≥ 0$.
  obtain ⟨d, hd_neg, hd_bound⟩ : ∃ d < 0, ∀ t ≥ 0, (orbitalDeriv V f (φ t)) ≤ d := by
    -- By the properties of the orbital derivative, there exists $d < 0$ such that $orbitalDeriv V f (φ t) ≤ d$ for all $t ≥ 0$ where $V(φ t) ≥ c$.
    obtain ⟨d, hd_neg, hd_bound⟩ : ∃ d < 0, ∀ x ∈ closedBall (0 : E) r, c ≤ V x → (orbitalDeriv V f x) ≤ d := by
      apply_rules [ orbitalDeriv_neg_bound ];
      exact hc.2;
    refine' ⟨ d, hd_neg, fun t ht => hd_bound _ ( hφball t ht ) _ ⟩;
    have h_antitone : AntitoneOn (V ∘ φ) (Set.Ici 0) := by
      apply_rules [ V_antitoneOn_trajectory ];
    exact le_of_tendsto hc.1 ( Filter.eventually_atTop.2 ⟨ t, fun u hu => h_antitone ( show 0 ≤ t by linarith ) ( show 0 ≤ u by linarith ) hu ⟩ );
  -- By the properties of the orbital derivative, we have $V(φ(T)) ≤ V(φ(0)) + d * T$ for all $T ≥ 0$.
  have h_linear_decay : ∀ T ≥ 0, (V ∘ φ) T ≤ (V ∘ φ) 0 + d * T := by
    apply_rules [ V_linear_decay ];
  -- Since $d < 0$, we have $d * T \to -\infty$ as $T \to \infty$.
  have h_dT_neg_inf : Filter.Tendsto (fun T : ℝ => d * T) Filter.atTop Filter.atBot := by
    exact Filter.tendsto_id.const_mul_atTop_of_neg hd_neg;
  exact not_tendsto_atBot_of_tendsto_nhds hc.1 ( Filter.tendsto_atTop_atBot.mpr fun x => by rcases Filter.eventually_atTop.mp ( h_dT_neg_inf.eventually ( Filter.eventually_lt_atBot ( x - ( V ∘ φ ) 0 ) ) ) with ⟨ T, hT ⟩ ; exact ⟨ Max.max T 0, fun t ht => by linarith [ h_linear_decay t ( le_trans ( le_max_right _ _ ) ht ), hT t ( le_trans ( le_max_left _ _ ) ht ) ] ⟩ )

/-! ## Part 1 – Lyapunov stability -/

/-
**Lyapunov stability (continuous-time).**
For every `ε > 0` there exists `δ > 0` such that every trajectory starting
with `‖x₀‖ < δ` satisfies `‖Φ(x₀, t)‖ < ε` for all `t ≥ 0`.
-/
theorem lyapunov_stability_ode
    {f : E → E} {V : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVdiff : ∀ x ∈ closedBall (0 : E) r, DifferentiableAt ℝ V x)
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdot : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → orbitalDeriv V f x < 0)
    (Φ : E → ℝ → E)
    (hΦinit : ∀ x₀ ∈ closedBall (0 : E) r, Φ x₀ 0 = x₀)
    (hΦode : ∀ x₀ ∈ closedBall (0 : E) r, ∀ t, 0 ≤ t →
      HasDerivAt (Φ x₀) (f (Φ x₀ t)) t)
    (hΦball : ∀ x₀ ∈ closedBall (0 : E) r, ∀ t, 0 ≤ t →
      Φ x₀ t ∈ closedBall (0 : E) r) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₀, ‖x₀‖ < δ →
      ∀ t, 0 ≤ t → ‖Φ x₀ t‖ < ε := by
  intro ε hε
  by_cases hε_le_r : ε ≤ r;
  · obtain ⟨ β, hβ_pos, hβ ⟩ := V_pos_lower_bound_annulus hr hε hε_le_r hVcont fun x hx hx' => hVpos x hx hx';
    -- By continuity of $V$ at $0$, there exists $\delta_1 > 0$ such that $\|x_0\| < \delta_1$ implies $V(x_0) < \beta$.
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x₀, ‖x₀‖ < δ₁ → V x₀ < β := by
      have := Metric.continuousAt_iff.mp ( show ContinuousAt V 0 from DifferentiableAt.continuousAt ( hVdiff 0 ( by simp +decide [ hr.le ] ) ) );
      exact Exists.elim ( this β hβ_pos ) fun δ hδ => ⟨ δ, hδ.1, fun x hx => by linarith [ abs_lt.mp ( hδ.2 ( show dist x 0 < δ from by simpa using hx ) ) ] ⟩;
    refine' ⟨ Min.min δ₁ r, lt_min hδ₁_pos hr, fun x₀ hx₀ t ht => _ ⟩;
    -- By the properties of the Lyapunov function, we have $V(\Phi(x₀, t)) \leq V(x₀)$ for all $t \geq 0$.
    have hV_le : ∀ t ≥ 0, V (Φ x₀ t) ≤ V x₀ := by
      have hV_le : AntitoneOn (V ∘ Φ x₀) (Set.Ici 0) := by
        apply_rules [ V_antitoneOn_trajectory ];
        · simpa using hx₀.le.trans ( min_le_right _ _ );
        · simpa using hx₀.le.trans ( min_le_right _ _ );
      exact fun t ht => by simpa [ hΦinit x₀ ( by simpa using hx₀.le.trans ( min_le_right _ _ ) ) ] using hV_le ( show 0 ∈ Ici 0 by norm_num ) ( show t ∈ Ici 0 by assumption ) ht;
    contrapose! hβ;
    exact ⟨ Φ x₀ t, hΦball x₀ ( by simpa using hx₀.le.trans ( min_le_right _ _ ) ) t ht, hβ, lt_of_le_of_lt ( hV_le t ht ) ( hδ₁ x₀ ( by simpa using hx₀.trans_le ( min_le_left _ _ ) ) ) ⟩;
  · exact ⟨ r, hr, fun x₀ hx₀ t ht => lt_of_le_of_lt ( mem_closedBall_zero_iff.mp ( hΦball x₀ ( mem_closedBall_zero_iff.mpr hx₀.le ) t ht ) ) ( not_le.mp hε_le_r ) ⟩

/-! ## Part 2 – Attractivity -/

/-
**Attractivity (continuous-time).**
There exists `δ > 0` such that every trajectory starting with `‖x₀‖ < δ`
converges to the origin as `t → +∞`.
-/
theorem lyapunov_attractivity_ode
    {f : E → E} {V : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVdiff : ∀ x ∈ closedBall (0 : E) r, DifferentiableAt ℝ V x)
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdot : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → orbitalDeriv V f x < 0)
    (hVdotCont : ContinuousOn (orbitalDeriv V f) (closedBall 0 r))
    (Φ : E → ℝ → E)
    (_hΦinit : ∀ x₀ ∈ closedBall (0 : E) r, Φ x₀ 0 = x₀)
    (hΦode : ∀ x₀ ∈ closedBall (0 : E) r, ∀ t, 0 ≤ t →
      HasDerivAt (Φ x₀) (f (Φ x₀ t)) t)
    (hΦball : ∀ x₀ ∈ closedBall (0 : E) r, ∀ t, 0 ≤ t →
      Φ x₀ t ∈ closedBall (0 : E) r) :
    ∃ δ > 0, ∀ x₀, ‖x₀‖ < δ →
      Tendsto (Φ x₀) atTop (nhds 0) := by
  refine' ⟨ r, hr, fun x₀ hx₀ => _ ⟩;
  -- By V_tendsto_zero_ode, V(Φ x₀ t) → 0 as t → ∞.
  have hV_zero : Filter.Tendsto (V ∘ Φ x₀) Filter.atTop (nhds 0) := by
    apply_rules [ V_tendsto_zero_ode ];
    · simpa using hx₀.le;
    · simpa using hx₀.le;
  -- To show Φ x₀ t → 0 in norm: for any ε > 0, we need ‖Φ x₀ t‖ < ε eventually. Use V_pos_lower_bound_annulus with min ε r to get β > 0 such that V(x) ≥ β whenever ‖x‖ ≥ min ε r and x ∈ closedBall 0 r.
  have h_bound : ∀ ε > 0, ∃ β > 0, ∀ x ∈ closedBall (0 : E) r, ε ≤ ‖x‖ → β ≤ V x := by
    intro ε hε_pos
    by_cases hεr : ε ≤ r;
    · exact V_pos_lower_bound_annulus hr hε_pos hεr hVcont hVpos;
    · exact ⟨ 1, zero_lt_one, fun x hx hx' => False.elim <| hεr <| hx'.trans <| by simpa using hx ⟩;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε; rcases h_bound ( Min.min ε r ) ( lt_min hε hr ) with ⟨ β, hβ, H ⟩ ; filter_upwards [ hV_zero β hβ, Filter.eventually_ge_atTop 0 ] with t ht ht' ; contrapose! ht ; simp_all +decide [ dist_eq_norm ] ;
  exact le_trans ( H _ ( hΦball _ hx₀.le _ ht' ) ( Or.inl ht ) ) ( le_abs_self _ )

/-! ## Main theorem – Asymptotic stability -/

/-- **Lyapunov asymptotic stability (continuous-time, Khalil Thm 4.1).**
Combines stability and attractivity into a single statement. -/
theorem lyapunov_asymptotic_stability_ode
    {f : E → E} {V : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hf0 : f 0 = 0) (hV0 : V 0 = 0)
    (hVcont : ContinuousOn V (closedBall 0 r))
    (hVdiff : ∀ x ∈ closedBall (0 : E) r, DifferentiableAt ℝ V x)
    (hVpos : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → 0 < V x)
    (hVdot : ∀ x ∈ closedBall (0 : E) r, x ≠ 0 → orbitalDeriv V f x < 0)
    (hVdotCont : ContinuousOn (orbitalDeriv V f) (closedBall 0 r))
    (Φ : E → ℝ → E)
    (hΦinit : ∀ x₀ ∈ closedBall (0 : E) r, Φ x₀ 0 = x₀)
    (hΦode : ∀ x₀ ∈ closedBall (0 : E) r, ∀ t, 0 ≤ t →
      HasDerivAt (Φ x₀) (f (Φ x₀ t)) t)
    (hΦball : ∀ x₀ ∈ closedBall (0 : E) r, ∀ t, 0 ≤ t →
      Φ x₀ t ∈ closedBall (0 : E) r) :
    (∀ ε > 0, ∃ δ > 0, ∀ x₀, ‖x₀‖ < δ →
      ∀ t, 0 ≤ t → ‖Φ x₀ t‖ < ε) ∧
    (∃ δ > 0, ∀ x₀, ‖x₀‖ < δ →
      Tendsto (Φ x₀) atTop (nhds 0)) :=
  ⟨lyapunov_stability_ode hr hf0 hV0 hVcont hVdiff hVpos hVdot
      Φ hΦinit hΦode hΦball,
   lyapunov_attractivity_ode hr hf0 hV0 hVcont hVdiff hVpos hVdot hVdotCont
      Φ hΦinit hΦode hΦball⟩

end Pythia.Control.LyapunovODE