/-
R1. TD(0) — baseline RL rule.

Invariants (spec/invariants.md §R1):
  I1a Convergence under Robbins-Monro + bounded rewards.
  I1b One-step support: a single reward at time t affects only V(s_{t-1}).
  I1c **Refutation**: TD(0) cannot produce a seconds-scale credit window
       from a single reward event (single-event credit kernel width ≤ Δt).

I1c is the key *negative* result for the Nature paper: TD(0) is refuted
against the Tang 2024 observation.
-/

import Pythia.Neuroscience.CreditAssignment.Basic
import Pythia.StochasticApproximation.Dvoretzky
import Mathlib

namespace Pythia.Neuroscience.CreditAssignment

namespace TD0

open Filter Topology

/-- TD(0) update: V(s_t) ← V(s_t) + α [r_{t+1} + γ V(s_{t+1}) - V(s_t)]. -/
noncomputable def tdUpdate
    (α γ : ℝ) (V : ValueFn)
    (s : State) (r : Reward) (s' : State) :
    ValueFn :=
  fun x => if x = s then V s + α * (r + γ * V s' - V s) else V x

/-- **I1a': TD(0) single-step update is bounded.** Real-content
    restatement of the convergence claim, closer to what we can prove
    without Mathlib's stochastic-approximation framework. The
    per-step change of `V s` is bounded by `α * (R_max + (1+γ) * V_max)`
    under bounded rewards + bounded values. Full stochastic
    convergence (the full I1a) is a corollary once the stochastic-
    approximation machinery lands; this bounded-update lemma is the
    analytical invariant TD(0) must satisfy. -/
theorem td0_single_step_bounded
    (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (V : ValueFn) (s s' : State) (r : Reward)
    (Rmax Vmax : ℝ) (hR : |r| ≤ Rmax) (hVs : |V s| ≤ Vmax)
    (hVs' : |V s'| ≤ Vmax) :
    |tdUpdate α γ V s r s' s - V s| ≤ α * (Rmax + (1 + γ) * Vmax) := by
  -- Direct: the difference equals α * (r + γ V(s') - V(s)); bound by
  -- triangle inequality. Let nlinarith discharge the arithmetic after
  -- we expose |r|, |V s|, |V s'| bounds and the definition.
  have h_eq : tdUpdate α γ V s r s' s - V s = α * (r + γ * V s' - V s) := by
    show (if s = s then V s + α * (r + γ * V s' - V s) else V s) - V s =
         α * (r + γ * V s' - V s)
    simp
  rw [h_eq, abs_mul, abs_of_nonneg hα]
  have h_r_lo : -Rmax ≤ r := (abs_le.mp hR).1
  have h_r_hi : r ≤ Rmax := (abs_le.mp hR).2
  have h_vs_lo : -Vmax ≤ V s := (abs_le.mp hVs).1
  have h_vs_hi : V s ≤ Vmax := (abs_le.mp hVs).2
  have h_vs'_lo : -Vmax ≤ V s' := (abs_le.mp hVs').1
  have h_vs'_hi : V s' ≤ Vmax := (abs_le.mp hVs').2
  apply mul_le_mul_of_nonneg_left _ hα
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith

/-- One-step support (I1b). A single reward `r_t` contributes ONLY to
    `V(s_{t-1})` via the update rule — propagation to earlier states
    requires subsequent updates. -/
theorem td0_one_step_support
    (α γ : ℝ) (V : ValueFn)
    (s s' : State) (r : Reward) (x : State) (hx : x ≠ s) :
    tdUpdate α γ V s r s' x = V x := by
  unfold tdUpdate
  split_ifs with h
  · exact absurd h hx
  · rfl

/-- **Refutation I1c**: the TD(0) single-event credit kernel has
    support width ≤ 1 time-step.

    Formal statement: for `x ≠ s`, applying `tdUpdate` to a new reward
    at state `s` does NOT change `V x`. Therefore no second-or-earlier
    state is reinforced by a single event.  -/
theorem td0_cannot_produce_temporal_window
    (α γ : ℝ) (V : ValueFn) (s s' : State) (r : Reward) :
    ∀ x : State, x ≠ s → tdUpdate α γ V s r s' x = V x := by
  intro x hx
  exact td0_one_step_support α γ V s s' r x hx

/-- Iterated TD(0) starting from `V₀`. -/
noncomputable def td0Iterate
    (α : StepSize) (γ : Discount)
    (τ : Trajectory) (V₀ : ValueFn) : ℕ → ValueFn
  | 0     => V₀
  | t + 1 =>
      tdUpdate (α.seq t) γ.val
        (td0Iterate α γ τ V₀ t)
        (τ.states t) (τ.rewards t) (τ.states (t + 1))

/-! ### Helper lemmas for TD(0) convergence -/

/-
For states not visited by the trajectory, the TD(0) iterate
    is unchanged from the initial value function.
-/
lemma td0_iterate_unvisited (α : StepSize) (γ : Discount)
    (τ : Trajectory) (V₀ : ValueFn) (s : State)
    (hSingle : ∀ t, τ.states t = τ.states 0)
    (hs : s ≠ τ.states 0) (t : ℕ) :
    td0Iterate α γ τ V₀ t s = V₀ s := by
  induction' t with t ih;
  · rfl;
  · rw [ show td0Iterate α γ τ V₀ ( t + 1 ) = fun x => if x = τ.states t then ( td0Iterate α γ τ V₀ t ) ( τ.states t ) + α.seq t * ( τ.rewards t + γ.val * ( td0Iterate α γ τ V₀ t ) ( τ.states ( t + 1 ) ) - ( td0Iterate α γ τ V₀ t ) ( τ.states t ) ) else ( td0Iterate α γ τ V₀ t ) x from rfl ] ; aesop

/-
Under a constant single-state trajectory, the value at the
    visited state satisfies a scalar affine recurrence.
-/
lemma td0_iterate_visited_recurrence (α : StepSize) (γ : Discount)
    (τ : Trajectory) (V₀ : ValueFn)
    (hSingle : ∀ t, τ.states t = τ.states 0)
    (hConstReward : ∀ t, τ.rewards t = τ.rewards 0) (t : ℕ) :
    td0Iterate α γ τ V₀ (t + 1) (τ.states 0) =
      (1 - α.seq t * (1 - γ.val)) *
        td0Iterate α γ τ V₀ t (τ.states 0) +
      α.seq t * τ.rewards 0 := by
  rw [ td0Iterate ];
  unfold tdUpdate; simp +decide [ hSingle, hConstReward ] ; ring;

/-
The error `V_t(s₀) − r/(1−γ)` satisfies a multiplicative
    contraction: `e_{t+1} = (1 − αₜ(1−γ)) · eₜ`.
-/
lemma td0_iterate_error_contraction (α : StepSize) (γ : Discount)
    (τ : Trajectory) (V₀ : ValueFn)
    (hSingle : ∀ t, τ.states t = τ.states 0)
    (hConstReward : ∀ t, τ.rewards t = τ.rewards 0)
    (hγ_ne : (1 : ℝ) - γ.val ≠ 0) (t : ℕ) :
    td0Iterate α γ τ V₀ (t + 1) (τ.states 0) -
      τ.rewards 0 / (1 - γ.val) =
    (1 - α.seq t * (1 - γ.val)) *
      (td0Iterate α γ τ V₀ t (τ.states 0) -
        τ.rewards 0 / (1 - γ.val)) := by
  have := td0_iterate_visited_recurrence α γ τ V₀ hSingle hConstReward t; norm_num [ tdUpdate ] at *; ring_nf at *; cases lt_or_gt_of_ne hγ_ne <;> nlinarith [ inv_mul_cancel_left₀ hγ_ne ( α.seq t * τ.rewards 0 ), inv_mul_cancel₀ hγ_ne ] ;

/-
Squared-error contraction: `eₜ₊₁² ≤ (1 − αₜ(1−γ)) · eₜ²`,
    which is the Robbins-Monro recurrence needed by
    `det_contraction_convergence`.
-/
lemma td0_sq_error_contraction (α : StepSize) (γ : Discount)
    (τ : Trajectory) (V₀ : ValueFn)
    (hSingle : ∀ t, τ.states t = τ.states 0)
    (hConstReward : ∀ t, τ.rewards t = τ.rewards 0)
    (hα_le : ∀ t, α.seq t ≤ 1)
    (hγ_ne : (1 : ℝ) - γ.val ≠ 0) (t : ℕ) :
    (td0Iterate α γ τ V₀ (t + 1) (τ.states 0) -
      τ.rewards 0 / (1 - γ.val)) ^ 2 ≤
    (1 - α.seq t * (1 - γ.val)) *
      (td0Iterate α γ τ V₀ t (τ.states 0) -
        τ.rewards 0 / (1 - γ.val)) ^ 2 := by
  rw [ td0_iterate_error_contraction α γ τ V₀ hSingle hConstReward hγ_ne t ];
  rw [ mul_pow ];
  exact mul_le_mul_of_nonneg_right ( pow_le_of_le_one ( sub_nonneg.2 <| mul_le_one₀ ( hα_le t ) ( sub_nonneg.2 γ.lt_one.le ) <| sub_le_self _ γ.nonneg ) ( sub_le_self _ <| mul_nonneg ( α.nonneg t ) <| sub_nonneg.2 γ.lt_one.le ) <| by norm_num ) <| sq_nonneg _

/-
The effective step-size sequence `αₜ(1−γ)` is not summable
    (diverges), inheriting from the original step-size divergence.
-/
lemma effective_step_not_summable (α : StepSize) (γ : Discount) :
    ¬Summable (fun t => α.seq t * (1 - γ.val)) := by
  rw [ summable_mul_right_iff ] <;> norm_num;
  · exact α.sumInf;
  · linarith [ γ.lt_one ]

/-
The effective step-size sequence `αₜ(1−γ)` has summable squares.
-/
lemma effective_step_sq_summable (α : StepSize) (γ : Discount) :
    Summable (fun t => (α.seq t * (1 - γ.val)) ^ 2) := by
  simpa only [ mul_pow ] using Summable.mul_right _ α.sumSq

/-
**I1a. TD(0) convergence** (content statement).

The original formulation (for arbitrary deterministic trajectories)
is false: a counter-example is a single-state, `γ = 0` trajectory
with rewards following a doubling-block pattern `(1,0,0,1,1,1,1,0,…)`,
for which the iterate equals the Cesàro mean of the rewards, which
oscillates between `1/3` and `2/3` indefinitely.

Under Robbins-Monro step sizes with `αₜ ≤ 1`, a **constant
single-state** trajectory with bounded rewards and `γ < 1`, iterated
TD(0) converges pointwise to the Bellman fixed point `r/(1−γ)`.

The proof reduces to
`Pythia.StochasticApproximation.Dvoretzky.det_contraction_convergence`
applied to the squared Bellman error.
-/
theorem td0_converges
    (α : StepSize) (γ : Discount)
    (τ : Trajectory) (hBounded : BoundedReward τ)
    (V₀ : ValueFn)
    (hα_le : ∀ t, α.seq t ≤ 1)
    (hSingle : ∀ t, τ.states t = τ.states 0)
    (hConstReward : ∀ t, τ.rewards t = τ.rewards 0) :
    ∃ V_star : ValueFn,
      ∀ s : State,
        Filter.Tendsto
          (fun t : ℕ => td0Iterate α γ τ V₀ t s)
          Filter.atTop (𝓝 (V_star s)) := by
  -- Define the limit function $V^*$.
  use fun s => if s = τ.states 0 then τ.rewards 0 / (1 - γ.val) else V₀ s;
  intro s
  by_cases hs : s = τ.states 0;
  · have h_sq_error_contraction : ∀ t, (td0Iterate α γ τ V₀ (t + 1) (τ.states 0) - τ.rewards 0 / (1 - γ.val)) ^ 2 ≤ (1 - α.seq t * (1 - γ.val)) * (td0Iterate α γ τ V₀ t (τ.states 0) - τ.rewards 0 / (1 - γ.val)) ^ 2 := by
      apply td0_sq_error_contraction α γ τ V₀ hSingle hConstReward hα_le;
      linarith [ γ.lt_one ];
    have := @Pythia.StochasticApproximation.Dvoretzky.det_contraction_convergence;
    specialize this ( fun t => ( td0Iterate α γ τ V₀ t ( τ.states 0 ) - τ.rewards 0 / ( 1 - γ.val ) ) ^ 2 ) ( fun t => α.seq t * ( 1 - γ.val ) ) ( fun t => 0 ) ; simp_all +decide [ summable_zero ];
    specialize this ( fun n => sq_nonneg _ ) ( fun n => mul_nonneg ( α.nonneg n ) ( sub_nonneg.mpr γ.lt_one.le ) ) ( fun n => mul_le_one₀ ( hα_le n ) ( sub_nonneg.mpr γ.lt_one.le ) ( sub_le_self _ γ.nonneg ) ) ( effective_step_not_summable α γ );
    exact tendsto_iff_norm_sub_tendsto_zero.mpr ( by simpa [ Real.sqrt_sq_eq_abs ] using this.sqrt );
  · simp [hs, td0_iterate_unvisited α γ τ V₀ s hSingle hs]

end TD0

end Pythia.Neuroscience.CreditAssignment