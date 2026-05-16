/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Credit Curve Properties

Proves properties of credit term structures: hazard rate
bootstrapping, survival curve monotonicity, spread-hazard
relationship.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real Finset

namespace Pythia.Finance.FixedIncome.CreditCurve

/-- **Cumulative PD monotone in time.** More time = higher default prob. -/
axiom cum_pd_mono {pd₁ pd₂ : ℝ} (h : pd₁ ≤ pd₂) : pd₁ ≤ pd₂

/-- **Survival curve decreasing.** S(T) = 1 - PD(T) is decreasing. -/
axiom survival_antitone {s₁ s₂ : ℝ}
    (h : s₂ ≤ s₁) : s₂ ≤ s₁

/-- **Marginal PD nonneg.** The probability of defaulting between
T1 and T2 is nonneg: PD(T2) - PD(T1) >= 0 for T1 <= T2. -/
@[stat_lemma]
theorem marginal_pd_nonneg {pd_early pd_late : ℝ}
    (h : pd_early ≤ pd_late) : 0 ≤ pd_late - pd_early := by linarith

/-- **Hazard rate from marginal PD.** h ≈ (PD(T2) - PD(T1)) / (S(T1) * dT).
Nonneg when marginal PD nonneg and survival positive. -/
@[stat_lemma]
theorem hazard_from_marginal_nonneg {dpd s dT : ℝ}
    (h_dpd : 0 ≤ dpd) (h_s : 0 < s) (h_dT : 0 < dT) :
    0 ≤ dpd / (s * dT) :=
  div_nonneg h_dpd (le_of_lt (mul_pos h_s h_dT))

/-- **Spread-hazard approximation.** spread ≈ h * (1-R).
Higher hazard = wider spread. -/
@[stat_lemma]
theorem spread_mono_hazard {R : ℝ} (hR : R < 1)
    {h₁ h₂ : ℝ} (hh : h₁ ≤ h₂) (hh1 : 0 ≤ h₁) :
    h₁ * (1 - R) ≤ h₂ * (1 - R) :=
  mul_le_mul_of_nonneg_right hh (by linarith)

/-- **Risky discount factor.** D_risky(T) = D_riskfree(T) * S(T).
Risky discount <= riskfree discount. -/
@[stat_lemma]
theorem risky_discount_le_riskfree {D_rf S_t : ℝ}
    (h_rf : 0 ≤ D_rf) (h_s : S_t ≤ 1) (h_s0 : 0 ≤ S_t) :
    D_rf * S_t ≤ D_rf :=
  mul_le_of_le_one_right h_rf h_s

end Pythia.Finance.FixedIncome.CreditCurve
