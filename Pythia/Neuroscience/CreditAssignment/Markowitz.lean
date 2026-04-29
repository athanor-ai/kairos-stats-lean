/-
Third-paradigm port: Markowitz et al. 2023 Nature,
"Spontaneous behaviour is structured by reinforcement without
explicit reward."
https://github.com/dattalab/dopamine-reinforces-spontaneous-behavior

The paradigm. Freely-moving mice emit behavioural "syllables" detected
by a MoSeq-style segmenter. Endogenous dopaminergic drift (not an
externally-delivered reward) reinforces the transition matrix over
syllables. The claimed computational mechanism is a Rescorla-Wagner-
style update on the per-syllable transition probability, gated by the
observed dopamine drift delta.

This port demonstrates that the Kairo scaffold (common types in
Basic.lean, eligibility-trace algebra, fleet-closure loop) transfers
to a paradigm whose update target is a stochastic matrix rather than
a value function. The point of the port is methodological: new
invariants, not new infrastructure.

Invariants (K1a-K1c, taking letter K after Markowitz):
  K1a row-sum preservation: updating a single transition probability
      preserves the row-stochastic property after normalization
  K1b boundedness: every transition probability stays in [0, 1]
      given sufficiently small step size and bounded dopamine signal
  K1c one-step support: a single dopamine drift event affects only the
      currently-emitted syllable pair
-/

import Pythia.Neuroscience.CreditAssignment.Basic

namespace Pythia.Neuroscience.CreditAssignment
namespace Markowitz

/-- A behavioural syllable (finite, discrete). Inherits the tabular
    representation used elsewhere in the Kairo scaffold. -/
abbrev Syllable := State

/-- Transition-probability table indexed by (s', s) = (previous, current). -/
abbrev TransitionMatrix := Syllable → Syllable → ℝ

/-- Markowitz-style update: reinforce the transition probability
    `P[s' → s]` by a Rescorla-Wagner increment proportional to the
    observed dopamine drift.
    Others are left untouched in the per-step rule; row re-normalization
    is a separate step the caller applies. -/
noncomputable def markowitzUpdate
    (α dopamineDrift : ℝ) (P : TransitionMatrix)
    (sPrev sCur : Syllable) : TransitionMatrix :=
  fun x y =>
    if x = sPrev ∧ y = sCur then
      P sPrev sCur + α * dopamineDrift
    else
      P x y

/-- **K1c one-step support.** A single Markowitz update touches only
    the (sPrev, sCur) cell; every other (x, y) pair is unchanged. -/
theorem markowitz_one_step_support
    (α dopamineDrift : ℝ) (P : TransitionMatrix)
    (sPrev sCur : Syllable) (x y : Syllable)
    (hxy : ¬ (x = sPrev ∧ y = sCur)) :
    markowitzUpdate α dopamineDrift P sPrev sCur x y = P x y := by
  unfold markowitzUpdate
  rw [if_neg hxy]

/-- **K1b bounded update magnitude.** For small `|α · δ|` the
    updated cell stays within `[0, 1]` when the original is in the
    safe interior. Concretely: if `P sPrev sCur ∈ [ε, 1 - ε]` and
    `|α · δ| ≤ ε`, the update stays in `[0, 1]`. -/
theorem markowitz_bounded_update
    (α dopamineDrift : ℝ) (P : TransitionMatrix)
    (sPrev sCur : Syllable)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (hP_lo : ε ≤ P sPrev sCur) (hP_hi : P sPrev sCur ≤ 1 - ε)
    (h_step : |α * dopamineDrift| ≤ ε) :
    0 ≤ markowitzUpdate α dopamineDrift P sPrev sCur sPrev sCur ∧
    markowitzUpdate α dopamineDrift P sPrev sCur sPrev sCur ≤ 1 := by
  unfold markowitzUpdate
  have hif : (if sPrev = sPrev ∧ sCur = sCur then
                  P sPrev sCur + α * dopamineDrift
              else P sPrev sCur)
           = P sPrev sCur + α * dopamineDrift := by
    rw [if_pos ⟨rfl, rfl⟩]
  rw [hif]
  have h_abs := abs_le.mp h_step
  refine ⟨?_, ?_⟩ <;> linarith

/-- **K1a row-sum preservation under compensatory offset.**
    A per-step increment of `α · δ` on the reinforced cell, compensated
    by redistributing `-α · δ` uniformly across the remaining `N - 1`
    cells of the row, keeps the row sum exactly equal to its initial
    value. This is the algebraic content of the row-stochasticity
    preservation hypothesis; full row-stochastic closure requires the
    caller to supply the offset step, which we leave separately
    to keep this theorem at the algebraic level. -/
theorem markowitz_row_sum_preserved
    (P_target_before P_increment : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (rest_before : Fin (N - 1) → ℝ)
    -- The reinforced cell moves by +P_increment
    -- The remaining N-1 cells each move by -P_increment / (N-1)
    (P_target_after : ℝ)
    (rest_after : Fin (N - 1) → ℝ)
    (h_target : P_target_after = P_target_before + P_increment)
    (h_rest : ∀ i, rest_after i = rest_before i - P_increment / (↑N - 1)) :
    P_target_after + (∑ i, rest_after i)
      = P_target_before + (∑ i, rest_before i) := by
  have h_N_pos : (0 : ℝ) < (↑N - 1) := by
    have : (2 : ℝ) ≤ (↑N : ℝ) := by exact_mod_cast hN
    linarith
  have h_sum : (∑ i : Fin (N - 1), rest_after i)
             = (∑ i, rest_before i) - (↑(N - 1) : ℝ) * (P_increment / (↑N - 1)) := by
    have h_pt : ∀ i, rest_after i = rest_before i - P_increment / (↑N - 1) := h_rest
    calc (∑ i : Fin (N - 1), rest_after i)
        = ∑ i : Fin (N - 1), (rest_before i - P_increment / (↑N - 1)) :=
          Finset.sum_congr rfl (fun i _ => h_pt i)
      _ = (∑ i, rest_before i)
            - (∑ _i : Fin (N - 1), P_increment / (↑N - 1)) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ i, rest_before i)
            - (↑(N - 1) : ℝ) * (P_increment / (↑N - 1)) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h_card : (↑(N - 1) : ℝ) = (↑N : ℝ) - 1 := by
    have h1 : 1 ≤ N := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [h_target, h_sum, h_card]
  have h_ne : ((↑N : ℝ) - 1) ≠ 0 := ne_of_gt h_N_pos
  have h_cancel : ((↑N : ℝ) - 1) * (P_increment / ((↑N : ℝ) - 1)) = P_increment := by
    field_simp
  rw [h_cancel]
  linarith

end Markowitz
end Pythia.Neuroscience.CreditAssignment
