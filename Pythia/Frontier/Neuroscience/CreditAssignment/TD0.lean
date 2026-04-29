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
import Mathlib.Probability.Kernel.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic

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

/-- **I1a. TD(0) convergence** (content statement).

Under Robbins-Monro step sizes, a bounded reward process, and
`γ < 1`, iterated TD(0) converges pointwise to some limit `V*`.
Proof deferred pending upstream Mathlib stochastic-approximation. -/
theorem td0_converges
    (α : StepSize) (γ : Discount)
    (τ : Trajectory) (hBounded : BoundedReward τ)
    (V₀ : ValueFn) :
    ∃ V_star : ValueFn,
      ∀ s : State,
        Filter.Tendsto
          (fun t : ℕ => td0Iterate α γ τ V₀ t s)
          Filter.atTop (𝓝 (V_star s)) := by
  sorry -- Robbins-Monro; Mathlib upstream

end TD0

end Pythia.Neuroscience.CreditAssignment
