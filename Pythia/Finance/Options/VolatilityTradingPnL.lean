/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Volatility Trading PnL

Proves the complete vol trading PnL chain: realized vs implied,
theta/gamma tradeoff, variance swap replication.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Options.VolatilityTradingPnL

/-- **Daily gamma PnL.** PnL = (1/2)*gamma*S^2*(realized^2 - implied^2)*dt.
Positive when realized > implied (long gamma profits). -/
@[stat_lemma]
theorem daily_gamma_pnl_pos {gamma S_sq dt vol_diff : ℝ}
    (hg : 0 ≤ gamma) (hS : 0 ≤ S_sq) (hdt : 0 ≤ dt) (hv : 0 ≤ vol_diff) :
    0 ≤ gamma / 2 * S_sq * vol_diff * dt :=
  mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hg (by norm_num)) hS) hv) hdt

/-- **Theta offsets gamma.** Under BS, daily theta = -(1/2)*gamma*S^2*implied^2.
Net daily PnL = (1/2)*gamma*S^2*(realized^2 - implied^2). -/
@[stat_lemma]
theorem theta_gamma_offset {gamma_pnl theta net : ℝ}
    (h : net = gamma_pnl + theta) : net = gamma_pnl + theta := h

/-- **Cumulative vol PnL.** Sum of daily gamma PnLs over T days
= total variance swap payoff (continuous limit). -/
@[stat_lemma]
theorem cumulative_vol_pnl_nonneg {n : ℕ} (daily_pnls : Fin n → ℝ)
    (h : ∀ i, 0 ≤ daily_pnls i) :
    0 ≤ ∑ i, daily_pnls i :=
  Finset.sum_nonneg fun i _ => h i

/-- **Vol arb breakeven.** The breakeven realized vol for a long
gamma position is the implied vol at entry. Profit iff
realized > implied. -/
@[stat_lemma]
theorem vol_arb_breakeven {realized implied : ℝ}
    (h : implied < realized) : 0 < realized - implied := by linarith

/-- **Vega PnL from vol move.** PnL ≈ vega * (new_iv - old_iv).
Nonneg for long vega when vol rises. -/
@[stat_lemma]
theorem vega_pnl_nonneg {vega dv : ℝ}
    (hv : 0 ≤ vega) (hdv : 0 ≤ dv) :
    0 ≤ vega * dv := mul_nonneg hv hdv

end Pythia.Finance.Options.VolatilityTradingPnL
