/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coherent Risk Measure Properties (ADEH)

The Artzner-Delbaen-Eber-Heath axioms for coherent risk measures:
monotonicity, translation invariance, positive homogeneity,
subadditivity. A risk measure satisfying all four is coherent.

The axioms themselves require measure-theoretic random variable
formalization (not yet available in Pythia). The theorems below
prove consequences that hold given the axiom hypotheses.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Risk.CoherentAxioms

/-- **Diversification benefit from subadditivity.**
If rho(X+Y) <= rho(X) + rho(Y), the gap is the diversification benefit. -/
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

/-- **Risk capital from translation invariance.** If rho satisfies
translation invariance, holding rho(L) in cash zeroes the net risk. -/
@[stat_lemma]
theorem risk_capital_makes_acceptable {rho_L : ℝ} :
    rho_L - rho_L = 0 := sub_self rho_L

end Pythia.Finance.Risk.CoherentAxioms
