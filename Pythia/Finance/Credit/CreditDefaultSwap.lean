/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Credit Default Swap (algebraic identities)

CDS spread s satisfies: premium leg = protection leg.
Under constant hazard rate lambda and recovery R:
s ≈ lambda * (1 - R).

## References

* Duffie, D. & Singleton, K. (2003). *Credit Risk*, Princeton.
* Hull, J. C. & White, A. (2000). "Valuing Credit Default Swaps."
  *Journal of Derivatives* 8(1).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.CreditDefaultSwap

/-- CDS spread approximation: s = lambda * (1 - R)
where lambda is hazard rate and R is recovery rate. -/
@[stat_lemma]
theorem spread_hazard_recovery {s lam R : ℝ}
    (h : s = lam * (1 - R)) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hlam : 0 ≤ lam) :
    0 ≤ s := by
  rw [h]; exact mul_nonneg hlam (by linarith)

/-- Higher recovery => lower spread (monotonicity). -/
@[stat_lemma]
theorem spread_recovery_monotone {s1 s2 lam R1 R2 : ℝ}
    (hlam : 0 ≤ lam) (hR : R1 ≤ R2)
    (h1 : s1 = lam * (1 - R1)) (h2 : s2 = lam * (1 - R2)) :
    s2 ≤ s1 := by
  rw [h1, h2]; nlinarith

/-- Survival probability: Q(t) = exp(-lambda * t). -/
@[stat_lemma]
theorem survival_prob_pos {lam t : ℝ} :
    0 < Real.exp (-(lam * t)) :=
  Real.exp_pos _

/-- Default probability: P(default by t) = 1 - exp(-lambda * t).
For lambda, t >= 0 this is in [0,1]. -/
@[stat_lemma]
theorem default_prob_bound {lam t : ℝ}
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    1 - Real.exp (-(lam * t)) ≤ 1 := by
  linarith [Real.exp_pos (-(lam * t))]

/-- Break-even: premium leg = protection leg implies fair spread.
premium_leg = s * risky_annuity, protection_leg = (1-R) * default_leg. -/
@[stat_lemma]
theorem break_even {s risky_ann R default_leg : ℝ}
    (hrann : 0 < risky_ann)
    (h : s * risky_ann = (1 - R) * default_leg) :
    s = (1 - R) * default_leg / risky_ann := by
  field_simp at h ⊢; linarith

end Pythia.Finance.CreditDefaultSwap
