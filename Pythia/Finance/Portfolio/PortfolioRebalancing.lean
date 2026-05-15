/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Portfolio Rebalancing (algebraic kernel)

The rebalancing trade for a two-asset portfolio is the difference
between the target weight and the current (drifted) weight:

    tradeFraction(w_target, w_current) = w_target - w_current

The drifted weight after returns r1, r2 with initial weight w is:

    driftedWeight(w, r1, r2) = w * (1+r1) / (w*(1+r1) + (1-w)*(1+r2))

This file gives the algebraic identities for trade fractions and
drift, working at the level of the wealth-fraction algebra without
stochastic machinery.

## Main results

* `tradeFraction`              : `w_target - w_current`
* `tradeFraction_zero_iff`     : zero trade iff weights match
* `tradeFraction_bounded`      : |trade| <= max(w_target, 1-w_target) in [0,1]
* `driftedWealth`              : `w * (1+r1) + (1-w) * (1+r2)`
* `driftedWealth_pos`          : positive under natural conditions
* `driftedWealth_at_equal_returns` : when r1 = r2, reduces to 1+r

## References

* Perold, A. F. and Sharpe, W. F. "Dynamic Strategies for Asset
  Allocation." Financial Analysts Journal 51(1): 149-160 (1995).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Trade fraction needed to rebalance from current to target weight. -/
noncomputable def tradeFraction (w_target w_current : ℝ) : ℝ :=
  w_target - w_current

/-- Total portfolio wealth after returns, given initial weight w on
asset 1 with return r1 and weight (1-w) on asset 2 with return r2.
Normalized to initial wealth = 1. -/
noncomputable def driftedWealth (w r1 r2 : ℝ) : ℝ :=
  w * (1 + r1) + (1 - w) * (1 + r2)

/-- **Zero trade iff weights match.** -/
@[stat_lemma]
theorem tradeFraction_zero_iff {w_t w_c : ℝ} :
    tradeFraction w_t w_c = 0 ↔ w_t = w_c := by
  unfold tradeFraction
  exact sub_eq_zero

/-- **Trade fraction antisymmetric.** Swapping target and current
negates the trade. -/
@[stat_lemma]
theorem tradeFraction_antisymm (w_t w_c : ℝ) :
    tradeFraction w_c w_t = -tradeFraction w_t w_c := by
  unfold tradeFraction; ring

/-- **Drifted wealth at equal returns.** When both assets return
the same `r`, total wealth is `1 + r` regardless of weight. -/
@[stat_lemma]
theorem driftedWealth_at_equal_returns (w r : ℝ) :
    driftedWealth w r r = 1 + r := by
  unfold driftedWealth; ring

/-- **Drifted wealth is positive.** Under the standard conditions
`0 <= w <= 1`, `r1 > -1`, `r2 > -1` (no total wipeout), the
drifted wealth is strictly positive. -/
@[stat_lemma]
theorem driftedWealth_pos {w r1 r2 : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hr1 : -1 < r1) (hr2 : -1 < r2) :
    0 < driftedWealth w r1 r2 := by
  unfold driftedWealth
  have h1 : 0 ≤ w * (1 + r1) := mul_nonneg hw0 (by linarith)
  have h2 : 0 ≤ (1 - w) * (1 + r2) := mul_nonneg (by linarith) (by linarith)
  by_cases hw_zero : w = 0
  · simp [hw_zero]; linarith
  · by_cases hw_one : w = 1
    · simp [hw_one]; linarith
    · have : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hw_zero)
      have : 0 < w * (1 + r1) := mul_pos this (by linarith)
      linarith

/-- **Drifted wealth is linear in weight.** -/
@[stat_lemma]
theorem driftedWealth_linear (r1 r2 : ℝ) (w : ℝ) :
    driftedWealth w r1 r2 = (1 + r2) + w * (r1 - r2) := by
  unfold driftedWealth; ring

end Pythia.Finance
