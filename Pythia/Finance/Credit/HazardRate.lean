/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hazard Rate Model (reduced-form credit)

Proves properties of the hazard rate (default intensity) model.
Survival probability S(T) = exp(-integral_0^T h(s) ds) for
constant hazard h: S(T) = exp(-h*T).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.Credit.HazardRate

/-- Survival probability under constant hazard rate. -/
noncomputable def survivalProb (h T : ℝ) : ℝ := Real.exp (-(h * T))

/-- Default probability = 1 - survival. -/
noncomputable def defaultProb (h T : ℝ) : ℝ := 1 - survivalProb h T

/-- **Survival probability positive.** exp is always positive. -/
@[stat_lemma]
theorem survivalProb_pos (h T : ℝ) : 0 < survivalProb h T :=
  Real.exp_pos _

/-- **Survival at time zero is 1.** No time elapsed means no default. -/
@[stat_lemma]
theorem survivalProb_at_zero (h : ℝ) : survivalProb h 0 = 1 := by
  unfold survivalProb; simp [mul_zero, neg_zero, Real.exp_zero]

/-- **Survival decreasing in time.** Longer horizon means lower
survival probability (for positive hazard rate). -/
@[stat_lemma]
theorem survivalProb_antitone {h : ℝ} (hh : 0 ≤ h)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    survivalProb h T₂ ≤ survivalProb h T₁ := by
  unfold survivalProb
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hT hh))

/-- **Survival at most 1.** -/
@[stat_lemma]
theorem survivalProb_le_one {h T : ℝ} (hh : 0 ≤ h) (hT : 0 ≤ T) :
    survivalProb h T ≤ 1 := by
  unfold survivalProb
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith [mul_nonneg hh hT])

/-- **Default probability in [0, 1].** -/
@[stat_lemma]
theorem defaultProb_nonneg {h T : ℝ} (hh : 0 ≤ h) (hT : 0 ≤ T) :
    0 ≤ defaultProb h T := by
  unfold defaultProb
  linarith [survivalProb_le_one hh hT]

@[stat_lemma]
theorem defaultProb_le_one (h T : ℝ) :
    defaultProb h T ≤ 1 := by
  unfold defaultProb
  linarith [survivalProb_pos h T]

/-- **Higher hazard means higher default probability.** -/
@[stat_lemma]
theorem defaultProb_mono_hazard {T : ℝ} (hT : 0 ≤ T)
    {h₁ h₂ : ℝ} (hh : h₁ ≤ h₂) (_hh1 : 0 ≤ h₁) :
    defaultProb h₁ T ≤ defaultProb h₂ T := by
  unfold defaultProb survivalProb
  have key : Real.exp (-(h₂ * T)) ≤ Real.exp (-(h₁ * T)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hh hT))
  linarith

/-- **CDS spread approximation.** For small default probability,
the CDS spread is approximately h * (1 - R) where R is recovery. -/
@[stat_lemma]
theorem cds_spread_nonneg {h R : ℝ}
    (hh : 0 ≤ h) (hR : R ≤ 1) :
    0 ≤ h * (1 - R) :=
  mul_nonneg hh (by linarith)

end Pythia.Finance.Credit.HazardRate
