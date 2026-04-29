/-
Pythia.Neuroscience.CableEquation -- passive cable equation steady-state
solution for a semi-infinite dendritic cable.

Reference: Rall, W. (1959). "Branching dendritic trees and motoneuron
membrane resistivity." Experimental Neurology 1(5):491-527.

The passive cable equation in steady state with input at x = 0
yields V(x) = V_0 * exp(-x / lambda), where lambda is the membrane
length constant. The solution decays exponentially in x.
-/
import Mathlib

namespace Pythia.Neuroscience

/-- Steady-state voltage on a passive semi-infinite cable: exponential
decay with length constant lambda. -/
noncomputable def cableSteadyState (V0 lambda x : ℝ) : ℝ :=
  V0 * Real.exp (-x / lambda)

/-- The cable steady-state solution at x = 0 equals the boundary voltage. -/
theorem cableSteadyState_at_zero (V0 lambda : ℝ) :
    cableSteadyState V0 lambda 0 = V0 := by
  simp [cableSteadyState]

/-- Voltage magnitude is monotone decreasing in distance for V0 ≥ 0
and lambda > 0. -/
theorem cableSteadyState_monotone_decreasing
    (V0 lambda : ℝ) (hV : 0 ≤ V0) (hlam : 0 < lambda)
    {x1 x2 : ℝ} (hx : x1 ≤ x2) :
    cableSteadyState V0 lambda x2 ≤ cableSteadyState V0 lambda x1 := by
  unfold cableSteadyState
  apply mul_le_mul_of_nonneg_left _ hV
  apply Real.exp_le_exp.mpr
  have hlam_inv : 0 < 1 / lambda := by positivity
  have h1 : -x2 / lambda = -x2 * (1 / lambda) := by ring
  have h2 : -x1 / lambda = -x1 * (1 / lambda) := by ring
  rw [h1, h2]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt hlam_inv)
  linarith

/-- Voltage is bounded above by V0 for nonneg V0, lambda > 0, x ≥ 0. -/
theorem cableSteadyState_bounded_by_input
    (V0 lambda x : ℝ) (hV : 0 ≤ V0) (hlam : 0 < lambda) (hx : 0 ≤ x) :
    cableSteadyState V0 lambda x ≤ V0 := by
  unfold cableSteadyState
  have hexp_le : Real.exp (-x / lambda) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · linarith
  calc V0 * Real.exp (-x / lambda)
      ≤ V0 * 1 := by exact mul_le_mul_of_nonneg_left hexp_le hV
    _ = V0 := by ring

end Pythia.Neuroscience
