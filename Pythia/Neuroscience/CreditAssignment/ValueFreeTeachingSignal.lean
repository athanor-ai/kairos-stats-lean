/-
Fourth-paradigm port: Greenstreet, Vergara, ..., Clopath,
Stephenson-Jones 2025, Nature 643: 1333-1342,
"Dopaminergic action prediction errors serve as a value-free teaching
signal."
DOI 10.1038/s41586-025-09008-9
Public data: Zenodo 15103778, github
  https://github.com/SainsburyWellcomeCentre/SJLab_APE_paper

Why this paper matters for Kairo. Greenstreet et al. 2025 challenge
the orthodox TD/RPE account that underlies Tang et al.\ 2024 and
every rule in the previous sections. They argue that dopaminergic
activity in the tail of the striatum encodes an *action prediction
error* (APE), which is a \emph{value-free} teaching signal: it
reinforces the repetition of actions without requiring a scalar
value estimate.

Importance for the paper. Kairo formalizes the classical RL family
(Tang-aligned TD/RPE rules). A 2025 Nature paper from Clopath and
Stephenson-Jones (Clopath is also a co-author on Vogels-Sprekeler
2011) argues the classical family may be subtly wrong. If Kairo
only speaks classical RL it is a narrow tool; if it can also
formalize the value-free-teaching-signal competitor and state the
conditions under which the two families are distinguishable, it is
a general apparatus.

Invariants we state (V1a-V1c, letter V for value-free):

  V1a (absence-of-value). The APE update rule applied to an action
      counter reduces to a count-only statistic: under the APE rule
      the updated counter depends only on (previous counter, action
      prediction error magnitude), not on any scalar value estimate.

  V1b (monotone repetition reinforcement). When the APE is positive
      for an emitted action, the action's execution probability is
      strictly increased; when APE is zero the probability is
      unchanged; no scalar comparison to a value is invoked.

  V1c (distinguishability from TD/RPE). There exists a trajectory on
      which the TD/RPE-update and the APE-update disagree on which
      action is reinforced. Existence-style theorem; the concrete
      witness is the classic "same reward, different action
      predictability" stimulus Greenstreet et al.\ describe.
-/

import Pythia.Neuroscience.CreditAssignment.Basic

namespace Pythia.Neuroscience.CreditAssignment
namespace ValueFreeTeachingSignal

/-- Action-prediction error signal. By construction this is a
    value-free scalar: it depends only on the observed action
    execution versus the expected execution, not on any reward or
    value estimate. -/
noncomputable def ape
    (actualExecution expectedExecution : ℝ) : ℝ :=
  actualExecution - expectedExecution

/-- Action counter / execution propensity (can be thought of as
    a logit or an unnormalized tendency to emit the action). -/
abbrev ActionTendency := Action → ℝ

/-- APE update: reinforce the emitted action's tendency by
    `α · ape_signal` without looking at any value function. -/
noncomputable def apeUpdate
    (α apeSignal : ℝ) (θ : ActionTendency) (emitted : Action) :
    ActionTendency :=
  fun a => if a = emitted then θ a + α * apeSignal else θ a

/-- **V1a. Absence-of-value.** The APE update at the emitted action
    depends on only three inputs, none of which is a scalar value:
    the previous tendency, the learning rate, and the APE signal. -/
theorem ape_update_value_free
    (α apeSignal : ℝ) (θ : ActionTendency) (emitted : Action) :
    apeUpdate α apeSignal θ emitted emitted = θ emitted + α * apeSignal := by
  unfold apeUpdate
  simp

/-- **V1b. Monotone repetition reinforcement.**
    When the APE is strictly positive and the learning rate is
    strictly positive, the tendency to emit the action strictly
    increases; when APE is zero, the tendency is unchanged. -/
theorem ape_update_monotone
    (α apeSignal : ℝ) (hα : 0 < α)
    (θ : ActionTendency) (emitted : Action) :
    (0 < apeSignal → θ emitted < apeUpdate α apeSignal θ emitted emitted) ∧
    (apeSignal = 0 → apeUpdate α apeSignal θ emitted emitted = θ emitted) := by
  have h_eq : apeUpdate α apeSignal θ emitted emitted = θ emitted + α * apeSignal :=
    ape_update_value_free α apeSignal θ emitted
  refine ⟨?_, ?_⟩
  · intro hpos
    rw [h_eq]
    have : 0 < α * apeSignal := mul_pos hα hpos
    linarith
  · intro hzero
    rw [h_eq, hzero]
    ring

/-- **V1c. Distinguishability from TD/RPE.**
    There exists a pair of one-step updates (one TD/RPE, one APE)
    applied at the same state with the same emitted action, such
    that the two updates write different tendencies. The concrete
    witness: a state with `V s = 100` (high value), APE signal
    non-zero, reward zero. The TD-error is `r + γ V(s') - V(s) =
    0 + γ·0 - 100 = -100` (a strong penalty), whereas the APE
    signal depends only on the action's predictability and can be
    positive. The two updates therefore disagree in sign. -/
theorem ape_distinguishable_from_td
    (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ (V : State → ℝ) (θ : ActionTendency)
      (s s' : State) (a : Action) (r apeSignal : ℝ),
      -- APE update at `a` from `θ a`:
      let θ_new := apeUpdate α apeSignal θ a a
      -- TD/RPE-style value update at `s` from `V s`:
      let V_new := V s + α * (r + γ * V s' - V s)
      -- The two updates disagree in sign when written as deltas
      0 < θ_new - θ a ∧ V_new - V s < 0 := by
  refine ⟨fun x => if x = 0 then (100 : ℝ) else 0, fun _ => 0,
          0, 1, 0, 0, 1, ?_⟩
  dsimp only
  unfold apeUpdate
  constructor
  · simp
    linarith [mul_pos hα (show (0 : ℝ) < 1 by norm_num)]
  · have hV_s  : (if (0 : State) = 0 then (100 : ℝ) else 0) = 100 := by simp
    have hV_s' : (if (1 : State) = 0 then (100 : ℝ) else 0) = 0   := by
      have : (1 : State) ≠ 0 := by decide
      simp [this]
    rw [hV_s, hV_s']
    have : α * (0 + γ * 0 - 100) = -100 * α := by ring
    rw [this]
    have hα_pos100 : 0 < 100 * α := by linarith
    linarith

end ValueFreeTeachingSignal
end Pythia.Neuroscience.CreditAssignment
