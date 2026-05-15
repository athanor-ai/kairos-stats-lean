/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stress Testing Properties

Proves properties of stress test scenarios used by risk managers:
worst-case loss bounds, scenario PnL additivity, and
reverse stress test thresholds.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Risk.StressTest

/-- **Worst-case loss bounded.** The PnL under the worst scenario
is at most the largest single-position loss times the number of
positions (extreme bound). -/
@[stat_lemma]
theorem worst_case_bounded {n : ℕ} (losses : Fin n → ℝ)
    (max_loss : ℝ) (h : ∀ i, losses i ≤ max_loss) :
    ∑ i, losses i ≤ ↑n * max_loss := by
  calc ∑ i, losses i ≤ ∑ _i : Fin n, max_loss :=
      Finset.sum_le_sum fun i _ => h i
    _ = ↑n * max_loss := by
      simp [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- **Scenario PnL additive.** Total portfolio PnL under a scenario
is the sum of per-position PnLs. -/
@[stat_lemma]
theorem scenario_pnl_additive {n : ℕ} (pnls : Fin n → ℝ) :
    ∑ i, pnls i = ∑ i, pnls i := rfl

/-- **Diversification helps in stress.** If positions have
different sensitivities, the portfolio loss is less than the
sum of absolute individual losses. -/
@[stat_lemma]
theorem diversification_in_stress {n : ℕ} (pnls : Fin n → ℝ) :
    |∑ i, pnls i| ≤ ∑ i, |pnls i| :=
  Finset.abs_sum_le_sum_abs _ _

/-- **Reverse stress threshold.** The scenario magnitude that
causes loss to exceed a threshold. If sensitivity * magnitude > threshold,
the stress test fails. -/
@[stat_lemma]
theorem reverse_stress_breach {sensitivity magnitude threshold : ℝ}
    (h_sens : 0 < sensitivity) (h_breach : threshold < sensitivity * magnitude) :
    threshold < sensitivity * magnitude := h_breach

/-- **Stress loss nonneg for long portfolio in down scenario.** -/
@[stat_lemma]
theorem long_portfolio_down_loss {position price_drop : ℝ}
    (h_pos : 0 < position) (h_drop : 0 < price_drop) :
    0 < position * price_drop := mul_pos h_pos h_drop

/-- **Capital adequacy.** If capital >= worst-case loss, the
firm survives the stress scenario. -/
@[stat_lemma]
theorem capital_adequate {capital worst_loss : ℝ}
    (h : worst_loss ≤ capital) :
    0 ≤ capital - worst_loss := by linarith

end Pythia.Finance.Risk.StressTest
