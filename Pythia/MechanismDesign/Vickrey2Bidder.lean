/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vickrey Second-Price Auction — Dominant Strategy (Two-Bidder)

## Main result

* `vickrey_second_price_dominant_strategy_two_bidder` — In a two-bidder
  second-price auction, truthful bidding (reporting `v_i`) weakly dominates
  any alternative bid `b_i`.  For any realization of the opponent's bid
  `b_other`, the payoff from bidding `v_i` is at least as large as the payoff
  from bidding `b_i`.

## Proof sketch

Four cases from `split_ifs` on the two indicator conditions:
1. `v_i > b_other` and `b_i > b_other`: both win; payoffs equal.
2. `v_i > b_other` and `¬ b_i > b_other`: truth wins, deviation loses;
   payoff difference = `v_i - b_other ≥ 0` (since `v_i > b_other`).
3. `¬ v_i > b_other` and `b_i > b_other`: deviation "wins" but at price
   `b_other ≥ v_i`, yielding non-positive surplus; truth pays 0.
4. `¬ v_i > b_other` and `¬ b_i > b_other`: both lose; payoffs equal.

In every case the inequality holds.  `linarith` closes each branch.

## References

* Vickrey, W. "Counterspeculation, Auctions, and Competitive Sealed Tenders".
  *Journal of Finance* 16(1): 8-37 (1961).
* Nisan, Roughgarden, Tardos, Vazirani. *Algorithmic Game Theory* Ch. 9 §9.2
  (Cambridge University Press, 2007).
-/
import Mathlib

namespace Pythia.MechanismDesign

set_option linter.unusedVariables false in
/-- **Vickrey SPA dominant strategy (two bidders).**
In a two-bidder second-price auction where bidder `i` has true value `v_i`
and the opponent bids `b_other`, truthful bidding weakly dominates any
alternative bid `b_i`.

The payoff function is `v_i - b_other` when the bidder wins (bid > `b_other`)
and `0` otherwise; the winner pays the opponent's bid.

Proof: four-case `split_ifs` analysis; each branch closes with `linarith`. -/
theorem vickrey_second_price_dominant_strategy_two_bidder
    (v_i b_other : ℝ) (h_v_nonneg : 0 ≤ v_i) :
    ∀ b_i : ℝ,
      (if v_i > b_other then v_i - b_other else 0) ≥
      (if b_i > b_other then v_i - b_other else 0) := by
  intro b_i
  split_ifs with h1 h2
  · -- Both win: payoffs equal.
    linarith
  · -- Truth wins, deviation loses: v_i - b_other ≥ 0.
    linarith
  · -- Deviation "wins" at loss: 0 ≥ v_i - b_other (since ¬ v_i > b_other).
    linarith [not_lt.mp h1]
  · -- Both lose: 0 ≥ 0.
    linarith

end Pythia.MechanismDesign
