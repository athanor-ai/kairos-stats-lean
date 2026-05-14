/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Herd Immunity Threshold

The critical vaccination fraction for disease eradication in the
basic SIR model. When the proportion of immune individuals exceeds
1 - 1/R₀, the effective reproduction number drops below 1 and the
disease cannot sustain an epidemic.

## References

* Anderson, R. M. & May, R. M. (1991): "Infectious Diseases of Humans."
* Hethcote, H. W. (2000): "The Mathematics of Infectious Diseases."
  SIAM Review 42(4), 599–653.

General applied mathematics.
-/
import Mathlib

open Real

noncomputable section

namespace Pythia.Epidemiology.HerdImmunity

/-- Basic reproduction number R₀: expected number of secondary
infections from one infectious individual in a fully susceptible
population. -/
structure EpidemicParams where
  β : ℝ     -- transmission rate
  γ : ℝ     -- recovery rate
  hβ : 0 < β
  hγ : 0 < γ

/-- R₀ = β/γ for the basic SIR model. -/
def R₀ (p : EpidemicParams) : ℝ := p.β / p.γ

/-- R₀ is positive when β, γ > 0. -/
theorem R₀_pos (p : EpidemicParams) : 0 < R₀ p := by
  exact div_pos p.hβ p.hγ

/-- Herd immunity threshold: the minimum fraction of the population
that must be immune to prevent sustained transmission. -/
def herdThreshold (p : EpidemicParams) : ℝ := 1 - 1 / R₀ p

/-- The herd immunity threshold is in [0, 1) when R₀ > 1. -/
theorem herdThreshold_nonneg (p : EpidemicParams) (hR : 1 < R₀ p) :
    0 ≤ herdThreshold p := by
  unfold herdThreshold
  have hR₀_pos := R₀_pos p
  rw [sub_nonneg]
  rw [div_le_iff hR₀_pos]
  linarith

theorem herdThreshold_lt_one (p : EpidemicParams) (hR : 1 < R₀ p) :
    herdThreshold p < 1 := by
  unfold herdThreshold
  linarith [div_pos one_pos (R₀_pos p)]

/-- **Effective reproduction number** under vaccination: R_eff = R₀ · (1 - v)
where v is the vaccination fraction. -/
def R_eff (p : EpidemicParams) (v : ℝ) : ℝ := R₀ p * (1 - v)

/-- When vaccination exceeds the herd threshold, R_eff < 1. -/
theorem R_eff_lt_one_of_vaccinated (p : EpidemicParams) (v : ℝ)
    (hR : 1 < R₀ p) (hv : herdThreshold p ≤ v) (hv1 : v ≤ 1) :
    R_eff p v < 1 := by
  unfold R_eff herdThreshold at *
  have hR₀_pos := R₀_pos p
  rw [← sub_pos]
  have h1 : R₀ p * (1 - v) - 1 < 0 := by
    have : 1 - 1 / R₀ p ≤ v := hv
    have : 1 - v ≤ 1 / R₀ p := by linarith
    have : R₀ p * (1 - v) ≤ R₀ p * (1 / R₀ p) := by
      apply mul_le_mul_of_nonneg_left this (le_of_lt hR₀_pos)
    rw [mul_one_div_cancel (ne_of_gt hR₀_pos)] at this
    linarith
  linarith

/-- When no one is vaccinated, R_eff = R₀. -/
theorem R_eff_zero (p : EpidemicParams) : R_eff p 0 = R₀ p := by
  unfold R_eff; ring

/-- When everyone is vaccinated, R_eff = 0. -/
theorem R_eff_one (p : EpidemicParams) : R_eff p 1 = 0 := by
  unfold R_eff; ring

/-- R_eff is monotone decreasing in vaccination fraction. -/
theorem R_eff_antitone (p : EpidemicParams) :
    Antitone (R_eff p) := by
  intro a b hab
  unfold R_eff
  have := R₀_pos p
  nlinarith

end Pythia.Epidemiology.HerdImmunity
