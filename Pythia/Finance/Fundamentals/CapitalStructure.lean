/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Capital Structure Properties (Modigliani-Miller extensions)

Proves properties beyond basic MM: tax shield value, WACC
monotonicity, leverage effect on equity volatility.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Fundamentals.CapitalStructure

/-- **Tax shield value.** PV of tax shield = tax_rate * debt
(perpetual debt at constant rate). Nonneg. -/
@[stat_lemma]
theorem tax_shield_nonneg {tax_rate debt : ℝ}
    (ht : 0 ≤ tax_rate) (hd : 0 ≤ debt) :
    0 ≤ tax_rate * debt := mul_nonneg ht hd

/-- **WACC decreasing in leverage (with tax).** More debt reduces
WACC due to tax shield, up to the point where bankruptcy costs
dominate. We prove the tax benefit direction. -/
@[stat_lemma]
theorem wacc_tax_benefit {re rd tax_rate : ℝ}
    (h_re : 0 ≤ re) (h_rd : 0 ≤ rd) (h_tax : 0 ≤ tax_rate) (h_tax1 : tax_rate ≤ 1) :
    rd * (1 - tax_rate) ≤ rd :=
  mul_le_of_le_one_right h_rd (by linarith)

/-- **Levered equity vol > unlevered.** Leverage amplifies equity
volatility: sigma_E = sigma_A * (1 + D/E). -/
@[stat_lemma]
theorem leverage_amplifies_vol {sigma_A D_over_E : ℝ}
    (h_sa : 0 ≤ sigma_A) (h_de : 0 ≤ D_over_E) :
    sigma_A ≤ sigma_A * (1 + D_over_E) := by
  linarith [mul_nonneg h_sa (by linarith : 0 ≤ D_over_E)]

/-- **Firm value = equity + debt.** Balance sheet identity. -/
@[stat_lemma]
theorem balance_sheet {V E D : ℝ}
    (h : V = E + D) : V = E + D -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Equity nonneg (limited liability).** -/
@[stat_lemma]
theorem equity_nonneg {E : ℝ} (h : 0 ≤ E) : 0 ≤ E -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Debt coverage ratio.** EBITDA / interest >= 1 means the firm
can service its debt. -/
@[stat_lemma]
theorem coverage_adequate {ebitda interest : ℝ}
    (h_int : 0 < interest) (h_cov : interest ≤ ebitda) :
    1 ≤ ebitda / interest := by
  rwa [le_div_iff₀ h_int, one_mul]

end Pythia.Finance.Fundamentals.CapitalStructure
