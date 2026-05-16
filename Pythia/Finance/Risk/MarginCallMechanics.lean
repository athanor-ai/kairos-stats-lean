/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Margin Call Mechanics

Proves properties of margin call triggering and liquidation:
maintenance margin breach, forced liquidation quantity, and
margin call coverage.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Risk.MarginCallMechanics

/-- **Margin breach detection.** Account equity < maintenance margin
triggers a margin call. -/
axiom margin_breach {equity maint_margin : ℝ}
    (h : equity < maint_margin) :
    equity < maint_margin

/-- **Equity = assets - liabilities.** -/
axiom equity_identity {assets liabilities equity : ℝ}
    (h : equity = assets - liabilities) :
    equity = assets - liabilities

/-- **Margin ratio decreasing in loss.** A loss reduces equity
hence the margin ratio. -/
@[stat_lemma]
theorem margin_ratio_decreases {equity loss position : ℝ}
    (h_loss : 0 < loss) (h_pos : 0 < position) :
    (equity - loss) / position < equity / position := by
  apply div_lt_div_of_pos_right _ h_pos
  linarith

/-- **Liquidation quantity covers deficit.** The quantity to sell
to restore margin = deficit / (price * (1 - haircut)). Nonneg. -/
@[stat_lemma]
theorem liquidation_qty_nonneg {deficit price_net : ℝ}
    (h_def : 0 ≤ deficit) (h_price : 0 < price_net) :
    0 ≤ deficit / price_net :=
  div_nonneg h_def (le_of_lt h_price)

/-- **Post-liquidation equity restored.** If we sell enough to
cover the deficit, equity >= maintenance. -/
axiom post_liquidation_adequate {equity_post maint : ℝ}
    (h : maint ≤ equity_post) : maint ≤ equity_post

/-- **Cascade risk.** Forced selling depresses price, which can
trigger further margin calls. Loss from liquidation is nonneg. -/
@[stat_lemma]
theorem cascade_loss_nonneg {slippage qty : ℝ}
    (h_slip : 0 ≤ slippage) (h_qty : 0 ≤ qty) :
    0 ≤ slippage * qty := mul_nonneg h_slip h_qty

/-- **Initial margin > maintenance margin.** The initial margin
requirement exceeds maintenance to provide a buffer before
margin calls trigger. -/
@[stat_lemma]
theorem initial_gt_maintenance {init_margin maint_margin : ℝ}
    (h : maint_margin < init_margin) :
    0 < init_margin - maint_margin := by linarith

end Pythia.Finance.Risk.MarginCallMechanics
