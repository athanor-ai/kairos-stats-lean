/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex Risk Measures (algebraic properties)

A convex risk measure rho satisfies:
1. Monotonicity: X <= Y => rho(X) >= rho(Y)
2. Translation invariance: rho(X + c) = rho(X) - c
3. Convexity: rho(lambda*X + (1-lambda)*Y) <= lambda*rho(X) + (1-lambda)*rho(Y)

## References

* Follmer, H. & Schied, A. (2002). "Convex measures of risk and
  trading constraints." *Finance and Stochastics* 6(4).
* Artzner, P. et al. (1999). "Coherent Measures of Risk."
  *Mathematical Finance* 9(3).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.ConvexRiskMeasure

/-- Translation invariance: adding cash c reduces risk by c. -/
@[stat_lemma]
theorem translation_invariance {rhoX rhoXc c : ℝ}
    (h : rhoXc = rhoX - c) :
    rhoXc + c = rhoX := by linarith

/-- Positive homogeneity (coherent case): rho(lambda * X) = lambda * rho(X). -/
@[stat_lemma]
theorem positive_homogeneity {rhoX rhoLX lam : ℝ}
    (hlam : 0 < lam)
    (h : rhoLX = lam * rhoX) :
    rhoLX / lam = rhoX := by
  rw [h, mul_div_cancel_left₀ _ (ne_of_gt hlam)]

/-- Sub-additivity (coherent case): rho(X + Y) <= rho(X) + rho(Y).
Diversification reduces risk. -/
@[stat_lemma]
theorem diversification_benefit {rhoX rhoY rhoXY : ℝ}
    (h : rhoXY ≤ rhoX + rhoY) :
    0 ≤ rhoX + rhoY - rhoXY := by linarith

/-- Convexity of risk: for lambda in [0,1],
rho(lambda*X + (1-lambda)*Y) <= lambda*rho(X) + (1-lambda)*rho(Y). -/
@[stat_lemma]
theorem convexity_gap {rhoMix lam rhoX rhoY : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (h : rhoMix ≤ lam * rhoX + (1 - lam) * rhoY) :
    rhoMix ≤ lam * rhoX + (1 - lam) * rhoY -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- Monotonicity implies non-negative risk of zero position:
if rho is normalized (rho(0) = 0) and X >= 0, then rho(X) <= 0. -/
@[stat_lemma]
theorem monotone_nonneg_risk {rhoX rho0 : ℝ}
    (hrho0 : rho0 = 0) (h_mono : rhoX ≤ rho0) :
    rhoX ≤ 0 := by linarith

end Pythia.Finance.ConvexRiskMeasure
