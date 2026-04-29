/-
Pythia.Neuroscience.HHGate -- Hodgkin-Huxley gating variable
steady-state and bounds.

Reference: Hodgkin, A.L., & Huxley, A.F. (1952). "A quantitative
description of membrane current and its application to conduction
and excitation in nerve." J. Physiol. 117(4):500-544.

A gating variable m in the Hodgkin-Huxley framework follows

  dm/dt = alpha(V) * (1 - m) - beta(V) * m,

with steady-state m_inf(V) = alpha / (alpha + beta), bounded in [0, 1]
for any nonneg alpha, beta with alpha + beta > 0.
-/
import Mathlib

namespace Pythia.Neuroscience

/-- Hodgkin-Huxley steady-state gating value m_inf = alpha / (alpha + beta). -/
noncomputable def hhGateSteadyState (alpha beta : ℝ) : ℝ :=
  alpha / (alpha + beta)

/-- Steady-state gating is nonneg when alpha, beta ≥ 0 and alpha + beta > 0. -/
theorem hhGateSteadyState_nonneg
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hsum : 0 < alpha + beta) :
    0 ≤ hhGateSteadyState alpha beta := by
  unfold hhGateSteadyState
  exact div_nonneg ha (le_of_lt hsum)

/-- Steady-state gating is at most 1. -/
theorem hhGateSteadyState_le_one
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hsum : 0 < alpha + beta) :
    hhGateSteadyState alpha beta ≤ 1 := by
  unfold hhGateSteadyState
  rw [div_le_one hsum]
  linarith

/-- Combined: gating value lies in [0, 1]. -/
theorem hhGateSteadyState_in_unit_interval
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hsum : 0 < alpha + beta) :
    0 ≤ hhGateSteadyState alpha beta ∧ hhGateSteadyState alpha beta ≤ 1 :=
  ⟨hhGateSteadyState_nonneg ha hb hsum,
   hhGateSteadyState_le_one ha hb hsum⟩

end Pythia.Neuroscience
