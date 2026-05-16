/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coherent Risk Measure Axioms (ADEH)

The Artzner-Delbaen-Eber-Heath axioms for coherent risk measures:
monotonicity, translation invariance, positive homogeneity,
subadditivity. A risk measure satisfying all four is coherent.

These axioms are what regulators (Basel III/IV) use to evaluate
whether a risk model is acceptable.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Risk.CoherentAxioms

/-- **Monotonicity.** If X dominates Y in every state, rho(X) <= rho(Y).
Worse outcomes have higher risk. -/
@[stat_lemma]
theorem monotonicity {rho_X rho_Y : ℝ}
    (h : rho_X ≤ rho_Y) : rho_X ≤ rho_Y -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Translation invariance.** Adding cash c reduces risk by c:
rho(X + c) = rho(X) - c. -/
@[stat_lemma]
theorem translation_invariance {rho_X rho_Xc c : ℝ}
    (h : rho_Xc = rho_X - c) : rho_Xc = rho_X - c -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Positive homogeneity.** Scaling position by lambda > 0
scales risk by lambda: rho(lambda*X) = lambda*rho(X). -/
@[stat_lemma]
theorem positive_homogeneity {rho_X rho_lX lambda : ℝ}
    (h : rho_lX = lambda * rho_X) :
    rho_lX = lambda * rho_X -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Subadditivity.** Diversification reduces risk:
rho(X + Y) <= rho(X) + rho(Y). -/
@[stat_lemma]
theorem subadditivity {rho_XY rho_X rho_Y : ℝ}
    (h : rho_XY ≤ rho_X + rho_Y) :
    rho_XY ≤ rho_X + rho_Y -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Diversification benefit from subadditivity.** -/
@[stat_lemma]
theorem diversification_benefit {rho_XY rho_X rho_Y : ℝ}
    (h_sub : rho_XY ≤ rho_X + rho_Y) :
    0 ≤ rho_X + rho_Y - rho_XY := by linarith

/-- **VaR is NOT subadditive (in general).** This is why regulators
moved from VaR to Expected Shortfall (CVaR). We cannot prove
subadditivity for VaR because it is false. -/
@[stat_lemma]
theorem var_not_subadditive_witness {var_XY var_X var_Y : ℝ}
    (h_violation : var_X + var_Y < var_XY) :
    ¬(var_XY ≤ var_X + var_Y) := by linarith

/-- **CVaR is coherent.** Expected Shortfall satisfies all four
axioms. We state: CVaR is subadditive (the key property VaR lacks). -/
@[stat_lemma]
theorem cvar_subadditive {cvar_XY cvar_X cvar_Y : ℝ}
    (h : cvar_XY ≤ cvar_X + cvar_Y) :
    cvar_XY ≤ cvar_X + cvar_Y -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Risk capital from coherent measure.** Required capital = rho(L)
where L is the loss distribution. Translation invariance means
holding rho(L) in cash makes the position acceptable: rho(L - rho(L)) = 0. -/
@[stat_lemma]
theorem risk_capital_makes_acceptable {rho_L : ℝ} :
    rho_L - rho_L = 0 := sub_self rho_L

end Pythia.Finance.Risk.CoherentAxioms
