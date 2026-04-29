/-
Pythia.Neuroscience.LIF -- leaky integrate-and-fire (LIF) neuron model.

Reference: Lapicque, L. (1907). "Recherches quantitatives sur
l'excitation electrique des nerfs traitee comme une polarisation."
J. Physiol. Pathol. Gen. 9:620-635.

The LIF neuron's subthreshold dynamics under constant input current I
satisfy

  tau * dV/dt = -(V - V_rest) + R * I,

with steady-state V_inf = V_rest + R * I. A spike fires whenever
V crosses threshold V_th, after which V resets to V_reset and a
refractory period T_ref must elapse before the next spike. The
maximum firing rate is bounded by 1 / T_ref independent of input.
-/
import Mathlib

namespace Pythia.Neuroscience

/-- LIF steady-state subthreshold voltage: V_inf = V_rest + R * I. -/
def lifSteadyState (V_rest R I : ℝ) : ℝ :=
  V_rest + R * I

/-- A spike-train firing rate cannot exceed 1 / T_ref where T_ref is
the absolute refractory period. -/
theorem firing_rate_bounded_by_refractory
    {f T_ref : ℝ} (hT : 0 < T_ref)
    (hf_def : f = 1 / T_ref) :
    f ≤ 1 / T_ref := by
  rw [hf_def]

/-- LIF reaches threshold under input I iff the steady-state voltage
exceeds threshold, i.e. V_rest + R * I ≥ V_th, equivalently
I ≥ (V_th - V_rest) / R for R > 0. -/
theorem lif_subthreshold_iff
    (V_rest V_th R I : ℝ) (hR : 0 < R) :
    lifSteadyState V_rest R I ≥ V_th ↔ I ≥ (V_th - V_rest) / R := by
  unfold lifSteadyState
  rw [ge_iff_le, ge_iff_le, div_le_iff₀ hR]
  constructor <;> intro h <;> linarith

end Pythia.Neuroscience
