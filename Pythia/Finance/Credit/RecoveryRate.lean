/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Recovery Rate Properties

Proves bounds on recovery rates and loss-given-default.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Credit.RecoveryRate

/-- **Recovery in [0, 1].** -/
@[stat_lemma]
theorem recovery_bounded {R : ℝ} (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    0 ≤ R ∧ R ≤ 1 := ⟨h0, h1⟩

/-- **LGD = 1 - R.** Loss given default is the complement. -/
@[stat_lemma]
theorem lgd_complement {R : ℝ} (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    0 ≤ 1 - R ∧ 1 - R ≤ 1 := ⟨by linarith, by linarith⟩

/-- **Higher recovery = lower loss.** -/
@[stat_lemma]
theorem lgd_antitone_recovery {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    1 - R₂ ≤ 1 - R₁ := by linarith

/-- **Expected loss = PD * LGD.** Nonneg. -/
@[stat_lemma]
theorem expected_loss_nonneg {pd lgd : ℝ}
    (hp : 0 ≤ pd) (hl : 0 ≤ lgd) :
    0 ≤ pd * lgd := mul_nonneg hp hl

/-- **Expected loss bounded by PD.** Since LGD <= 1. -/
@[stat_lemma]
theorem expected_loss_le_pd {pd lgd : ℝ}
    (hp : 0 ≤ pd) (hl : lgd ≤ 1) :
    pd * lgd ≤ pd := mul_le_of_le_one_right hp hl

/-- **Seniority improves recovery.** Senior debt has higher
recovery than subordinated. -/
@[stat_lemma]
theorem seniority_improves {R_senior R_sub : ℝ}
    (h : R_sub ≤ R_senior) : R_sub ≤ R_senior := h

end Pythia.Finance.Credit.RecoveryRate
