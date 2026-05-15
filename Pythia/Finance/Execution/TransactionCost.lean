/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proportional Transaction Cost Model

The *proportional transaction cost model* prices each trade at a fixed
fraction of notional.  For a trade of size `Q` (signed) at cost rate
`c`, the implementation-shortfall cost is

    cost(c, Q) = c * |Q|.

The cost is proportional to the absolute trade size and to the rate `c`.
After subtracting transaction costs, the net return on a strategy with
gross return `r`, cost rate `c`, and portfolio turnover `turnover` is

    netReturn(r, c, turnover) = r - c * turnover.

This module gives the algebraic properties of both functions:
non-negativity, zero-crossing, sign symmetry, rate monotonicity, and
the gross-vs-net inequality.

## Main definitions

* `proportionalCost` : `c * |Q|`
* `netReturn`        : `r - c * turnover`

## Main results

* `proportionalCost_nonneg`          : `c >= 0 -> proportionalCost c Q >= 0`
* `proportionalCost_zero_at_zero_trade` : `proportionalCost c 0 = 0`
* `proportionalCost_symm`            : cost is even in `Q`
* `proportionalCost_mono_rate`       : monotone in `c` for fixed `Q`
* `netReturn_le_gross`               : `c >= 0, turnover >= 0 -> netReturn <= r`
* `netReturn_at_zero_cost`           : `netReturn r 0 turnover = r`

## References

* Perold, A. F. "The Implementation Shortfall."
  *Journal of Portfolio Management* 14(3): 4-9 (1988).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Proportional transaction cost: `c * |Q|`.

Here `c` is the cost rate (bid-ask half-spread, commission rate, or
estimated market-impact coefficient expressed as a fraction of
notional) and `Q` is the signed trade size.  The absolute value
captures that both buys and sells incur the same cost. -/
noncomputable def proportionalCost (c Q : ℝ) : ℝ :=
  c * |Q|

/-- Net return after transaction costs: `r - c * turnover`.

Here `r` is the gross portfolio return, `c` is the cost rate, and
`turnover` is the one-way turnover (sum of absolute weight changes).
This is the *implementation shortfall* in return space. -/
noncomputable def netReturn (r c turnover : ℝ) : ℝ :=
  r - c * turnover

/-- **Non-negativity of cost.** For a non-negative cost rate, the
proportional transaction cost is non-negative regardless of trade
direction. -/
@[stat_lemma]
theorem proportionalCost_nonneg {c : ℝ} (hc : 0 ≤ c) (Q : ℝ) :
    0 ≤ proportionalCost c Q := by
  unfold proportionalCost
  exact mul_nonneg hc (abs_nonneg Q)

/-- **Zero cost at zero trade.** No trading incurs no transaction cost,
for any cost rate `c`. -/
@[stat_lemma]
theorem proportionalCost_zero_at_zero_trade (c : ℝ) :
    proportionalCost c 0 = 0 := by
  unfold proportionalCost
  simp [abs_zero]

/-- **Symmetry in trade direction.** Buying and selling the same
absolute quantity incur identical costs: the cost function is even in
`Q`. -/
@[stat_lemma]
theorem proportionalCost_symm (c Q : ℝ) :
    proportionalCost c Q = proportionalCost c (-Q) := by
  unfold proportionalCost
  rw [abs_neg]

/-- **Monotone in cost rate.** For fixed trade size `Q`, a higher cost
rate `c2` produces a weakly higher proportional transaction cost than
`c1 <= c2`. The proof uses `mul_le_mul_of_nonneg_right` with the
non-negativity of `|Q|`. -/
@[stat_lemma]
theorem proportionalCost_mono_rate {c1 c2 : ℝ} (h : c1 ≤ c2) (Q : ℝ) :
    proportionalCost c1 Q ≤ proportionalCost c2 Q := by
  unfold proportionalCost
  exact mul_le_mul_of_nonneg_right h (abs_nonneg Q)

/-- **Net return is at most gross return.** When the cost rate and
turnover are both non-negative, the transaction cost is non-negative,
so the net return cannot exceed the gross return. -/
@[stat_lemma]
theorem netReturn_le_gross {c turnover : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ turnover)
    (r : ℝ) :
    netReturn r c turnover ≤ r := by
  unfold netReturn
  exact sub_le_self r (mul_nonneg hc ht)

/-- **Zero-cost specialisation.** At zero cost rate, the net return
equals the gross return: no costs to pay. -/
@[stat_lemma]
theorem netReturn_at_zero_cost (r turnover : ℝ) :
    netReturn r 0 turnover = r := by
  unfold netReturn
  ring

end Pythia.Finance
