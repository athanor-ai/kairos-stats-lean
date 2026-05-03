/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SEIR Epidemiological Model — R₀ Sub-threshold Condition

In the SEIR (Susceptible-Exposed-Infectious-Recovered) model, the basic reproduction
number R₀ = β/γ determines whether an epidemic grows (R₀ > 1) or declines (R₀ ≤ 1).
When R₀·S ≤ 1, the infectious compartment does not grow: β·S·I - γ·I ≤ 0.

## Main results

* `seir_r0_threshold` — when β·S/γ ≤ 1, the net infectious rate β·S·I - γ·I ≤ 0.

## References

* Anderson, R.M. and May, R.M. *Infectious Diseases of Humans: Dynamics and Control*.
  Oxford University Press (1991), Ch. 2.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Bio.SEIR

/-!
## SEIR R₀ threshold condition

The SEIR model tracks four compartments S, E, I, R with dynamics:

    dS/dt = -β·S·I
    dE/dt = β·S·I - σ·E
    dI/dt = σ·E - γ·I
    dR/dt = γ·I

The basic reproduction number is R₀ = β/γ. When R₀·S ≤ 1 (i.e., β·S ≤ γ), the
infectious compartment cannot increase: the σ·E → I inflow is insufficient to
overcome γ·I removal when evaluated at the instantaneous net forcing β·S·I - γ·I ≤ 0.
-/

/-- The basic reproduction number for the SEIR model: ratio of transmission rate to
recovery rate. -/
noncomputable def seirR0 (β γ : ℝ) : ℝ := β / γ

/-- **SEIR R₀ sub-threshold condition.**
When the effective reproduction number `R₀·S = (β/γ)·S ≤ 1`, the net infectious
forcing `β·S·I - γ·I` is non-positive for any positive infectious compartment `I`. -/
@[stat_lemma]
theorem seir_r0_threshold {β σ γ S E I : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hγ : 0 < γ)
    (hS : 0 ≤ S) (hI : 0 < I) (hR0 : seirR0 β γ * S ≤ 1) :
    β * S * I - γ * I ≤ 0 := by
  unfold seirR0 at hR0
  rw [div_mul_eq_mul_div, div_le_one hγ] at hR0
  nlinarith

end Pythia.Bio.SEIR
