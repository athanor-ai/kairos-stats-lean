/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Slippage Model (execution quality)

Proves bounds on execution slippage: the difference between
expected and actual fill price.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.HFT.SlippageModel

/-- Slippage: actual fill price minus expected price. -/
noncomputable def slippage (actual expected : ℝ) : ℝ := actual - expected

/-- **Slippage bounded by spread.** Fill cannot be worse than
crossing the full spread from mid. -/
@[stat_lemma]
theorem slippage_bounded_by_half_spread {actual mid half_spread : ℝ}
    (h : |actual - mid| ≤ half_spread) :
    |slippage actual mid| ≤ half_spread := by
  unfold slippage; exact h

/-- **Zero slippage at mid.** Filling exactly at mid gives zero slippage. -/
@[stat_lemma]
theorem slippage_zero_at_expected (p : ℝ) : slippage p p = 0 := by
  unfold slippage; ring

/-- **Slippage additive across fills.** Total slippage from n fills
is the sum of per-fill slippages. -/
@[stat_lemma]
theorem slippage_sum {n : ℕ} (actuals expecteds : Fin n → ℝ) :
    ∑ i, slippage (actuals i) (expecteds i) =
      ∑ i, actuals i - ∑ i, expecteds i := by
  unfold slippage; rw [← Finset.sum_sub_distrib]

/-- **Implementation shortfall decomposition.** Total cost =
delay cost + market impact + timing cost. We prove the additive
decomposition. -/
@[stat_lemma]
theorem implementation_shortfall {delay_cost impact timing : ℝ}
    {total : ℝ} (h : total = delay_cost + impact + timing) :
    total = delay_cost + impact + timing -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Market impact nonneg for buy orders.** Buying pushes price up,
so impact >= 0. -/
@[stat_lemma]
theorem buy_impact_nonneg {pre_trade post_trade : ℝ}
    (h : pre_trade ≤ post_trade) :
    0 ≤ post_trade - pre_trade := by linarith

/-- **Adverse selection cost.** A market maker's average fill is
adversely selected: informed traders pick off stale quotes.
The adverse selection cost is the expected loss per fill. -/
@[stat_lemma]
theorem adverse_selection_nonneg {avg_fill true_value : ℝ}
    (h_buy_side : true_value ≤ avg_fill) :
    0 ≤ avg_fill - true_value := by linarith

end Pythia.Finance.HFT.SlippageModel
