/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Liquidity Risk Properties

Bid-ask spread, market depth, and liquidity-adjusted VaR.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Risk.LiquidityRisk

/-- **Liquidity cost nonneg.** Crossing the spread always costs. -/
@[stat_lemma]
theorem liquidity_cost_nonneg {half_spread qty : ℝ}
    (hs : 0 ≤ half_spread) (hq : 0 ≤ qty) :
    0 ≤ half_spread * qty := mul_nonneg hs hq

/-- **Liquidity cost monotone in size.** Larger trades cost more. -/
@[stat_lemma]
theorem liquidity_cost_mono {half_spread : ℝ} (hs : 0 ≤ half_spread)
    {q₁ q₂ : ℝ} (h : q₁ ≤ q₂) :
    half_spread * q₁ ≤ half_spread * q₂ :=
  mul_le_mul_of_nonneg_left h hs

/-- **LVaR >= VaR.** Liquidity-adjusted VaR adds the liquidation
cost to the market risk VaR. -/
@[stat_lemma]
theorem lvar_ge_var {var liq_cost : ℝ} (h : 0 ≤ liq_cost) :
    var ≤ var + liq_cost := le_add_of_nonneg_right h

/-- **Wider spread = higher LVaR.** -/
@[stat_lemma]
theorem lvar_mono_spread {var qty : ℝ} (hq : 0 ≤ qty)
    {s₁ s₂ : ℝ} (h : s₁ ≤ s₂) :
    var + s₁ * qty ≤ var + s₂ * qty := by
  linarith [mul_le_mul_of_nonneg_right h hq]

/-- **Illiquidity discount.** An illiquid asset is worth less than
its mark-to-market value by the liquidation cost. -/
@[stat_lemma]
theorem illiquidity_discount {mtm liq_cost : ℝ} (h : 0 ≤ liq_cost) :
    mtm - liq_cost ≤ mtm := sub_le_self mtm h

end Pythia.Finance.Risk.LiquidityRisk
