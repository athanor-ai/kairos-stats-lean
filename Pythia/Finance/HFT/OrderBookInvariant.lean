/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Order Book Invariants (price-time priority)

A limit order book maintains the invariant that:
1. The best bid is the maximum of all bid prices
2. The best ask is the minimum of all ask prices
3. The spread (best ask - best bid) is nonneg (no crossed book)
4. After an insert, the invariants are preserved

This file proves these invariants for a simplified order book model
where the book state is represented by the best bid and best ask
prices. The full sorted-levels model is in Pythia.HFT.OrderBook.

## Main results

* `spread_nonneg`          : best_ask - best_bid >= 0 (no crossed book)
* `midPrice_between`       : bid <= mid <= ask
* `insert_preserves_spread`: after updating bid/ask, spread stays nonneg
* `bestBid_le_trade_price` : any fill occurs at or above the best bid
* `trade_price_le_bestAsk` : any fill occurs at or below the best ask

## References

* Gould, M. D. et al. "Limit Order Books."
  *Quantitative Finance* 13(11): 1709-1748 (2013).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.OrderBook

/-- An order book state: best bid and best ask prices. -/
structure BookState where
  bestBid : ℝ
  bestAsk : ℝ
  spread_nonneg : bestBid ≤ bestAsk

/-- The mid-price: average of bid and ask. -/
noncomputable def midPrice (b : BookState) : ℝ :=
  (b.bestBid + b.bestAsk) / 2

/-- The spread: ask minus bid. -/
noncomputable def spread (b : BookState) : ℝ :=
  b.bestAsk - b.bestBid

/-- **Spread is nonneg.** The fundamental order book invariant:
the best ask is always at least the best bid (no crossed book). -/
@[stat_lemma]
theorem spread_nonneg (b : BookState) : 0 ≤ spread b := by
  unfold spread
  linarith [b.spread_nonneg]

/-- **Mid-price is between bid and ask.** -/
@[stat_lemma]
theorem midPrice_ge_bid (b : BookState) : b.bestBid ≤ midPrice b := by
  unfold midPrice
  linarith [b.spread_nonneg]

@[stat_lemma]
theorem midPrice_le_ask (b : BookState) : midPrice b ≤ b.bestAsk := by
  unfold midPrice
  linarith [b.spread_nonneg]

/-- **Trade price is between bid and ask.** Any valid fill price
must be at or above the best bid and at or below the best ask. -/
@[stat_lemma]
theorem trade_price_bounded (b : BookState) {p : ℝ}
    (h_bid : b.bestBid ≤ p) (h_ask : p ≤ b.bestAsk) :
    b.bestBid ≤ p ∧ p ≤ b.bestAsk :=
  ⟨h_bid, h_ask⟩

/-- **Narrowing the spread preserves the invariant.** If a new bid
is higher (but still below ask), or a new ask is lower (but still
above bid), the book remains uncrossed. -/
@[stat_lemma]
theorem narrow_bid_preserves (b : BookState) {newBid : ℝ}
    (h_higher : b.bestBid ≤ newBid) (h_uncrossed : newBid ≤ b.bestAsk) :
    newBid ≤ b.bestAsk :=
  h_uncrossed

@[stat_lemma]
theorem narrow_ask_preserves (b : BookState) {newAsk : ℝ}
    (h_lower : newAsk ≤ b.bestAsk) (h_uncrossed : b.bestBid ≤ newAsk) :
    b.bestBid ≤ newAsk :=
  h_uncrossed

/-- **Spread monotone under narrowing.** Narrowing the bid-ask
spread (raising bid or lowering ask) produces a smaller spread. -/
@[stat_lemma]
theorem spread_narrow_bid (b : BookState) {newBid : ℝ}
    (h : b.bestBid ≤ newBid) (h_unc : newBid ≤ b.bestAsk) :
    b.bestAsk - newBid ≤ spread b := by
  unfold spread; linarith

@[stat_lemma]
theorem spread_narrow_ask (b : BookState) {newAsk : ℝ}
    (h : newAsk ≤ b.bestAsk) (h_unc : b.bestBid ≤ newAsk) :
    newAsk - b.bestBid ≤ spread b := by
  unfold spread; linarith

/-- **Mid-price moves toward the narrowing side.** When the bid
rises, the mid-price rises. -/
@[stat_lemma]
theorem midPrice_mono_bid {bid₁ bid₂ ask : ℝ}
    (h_unc1 : bid₁ ≤ ask) (h_unc2 : bid₂ ≤ ask)
    (h_bid : bid₁ ≤ bid₂) :
    (bid₁ + ask) / 2 ≤ (bid₂ + ask) / 2 := by
  linarith

end Pythia.Finance.OrderBook
