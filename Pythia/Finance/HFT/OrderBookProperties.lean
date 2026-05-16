/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Order Book Properties — Price Structure Theorems

Formal proofs of the core price-level properties that every limit
order book must satisfy. These are the foundational invariants that
execution algorithms and risk systems depend on.

## Main results

* `spread_nonneg`             : spread = ask - bid ≥ 0 when ask ≥ bid
* `mid_between_bid_ask`       : bid ≤ mid ≤ ask where mid = (bid + ask) / 2
* `tighter_spread_lower_cost` : for fixed quantity, narrower spread means lower round-trip cost
* `vwmp_bounded_by_bid_ask`   : volume-weighted mid price lies in [bid, ask]

## Why this matters for HFT

* Market-making profitability rests on capturing the spread; a
  negative spread would imply a crossed book and is immediately
  rejected by a correct matching engine.
* The mid-price bound is the reference price for virtually every
  execution algorithm. Algorithms that assume mid is between the
  quotes must have that assumption proved, not assumed.
* Spread minimization is the primary liquidity metric. The tighter-
  spread theorem translates spread improvement into cost savings,
  quantifying the value of queue position.
* Volume-weighted mid price is a common fair-value estimate for
  thin markets. Bounding it between bid and ask prevents the
  estimate from implying synthetic arbitrage.

## References

* Gould, M. D. et al. (2013). "Limit order books."
  *Quantitative Finance* 13(11): 1709--1742.
* Harris, L. (2003). *Trading and Exchanges: Market Microstructure
  for Practitioners*. Oxford University Press.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.HFT.OrderBookProperties

/-! ## Section 1 — Spread Definition and Non-negativity

The bid-ask spread is the difference between the best ask price and
the best bid price. In a valid (non-crossed) order book the ask is
always at least as large as the bid, so the spread is non-negative.
A spread of exactly zero means the book is crossed (or a trade should
have occurred), so positive spread is the normal steady state. -/

/-- **Spread definition.** The bid-ask spread is ask minus bid.
This is the round-trip cost per share for a market order that buys
at the ask and sells at the bid. -/
noncomputable def spread (bid ask : ℝ) : ℝ := ask - bid

/-- **Spread is non-negative** when ask ≥ bid. This is the fundamental
no-crossed-book invariant: a valid order book always has ask ≥ bid,
which forces spread ≥ 0.

Proof uses `linarith` after unfolding the definition. -/
@[stat_lemma]
theorem spread_nonneg {bid ask : ℝ} (h : bid ≤ ask) :
    0 ≤ spread bid ask := by
  unfold spread
  linarith

/-- **Spread is strictly positive** when bid < ask (the generic case).
A positive spread means the book is not crossed and there is a cost
to immediacy. -/
@[stat_lemma]
theorem spread_pos {bid ask : ℝ} (h : bid < ask) :
    0 < spread bid ask := by
  unfold spread
  linarith

/-- **Spread is zero iff bid equals ask.** The book is at the crossing
point precisely when bid = ask — every market order would get a free fill.
This is the degenerate case that a matching engine resolves immediately. -/
@[stat_lemma]
theorem spread_eq_zero_iff {bid ask : ℝ} (h : bid ≤ ask) :
    spread bid ask = 0 ↔ bid = ask := by
  unfold spread
  constructor
  · intro heq; linarith
  · intro heq; linarith

/-! ## Section 2 — Mid-Price is Between Bid and Ask

The mid-price is the arithmetic average of bid and ask. It is the
standard reference price for execution benchmarks, fair-value
estimates, and signal computation. A correct implementation must
guarantee that mid lies in [bid, ask]. -/

/-- **Mid-price definition.** The mid-price is the arithmetic mean of
bid and ask. -/
noncomputable def midPrice (bid ask : ℝ) : ℝ := (bid + ask) / 2

/-- **Mid-price lies between bid and ask.** When ask ≥ bid, the
mid-price satisfies bid ≤ mid ≤ ask. This is the fundamental
sanity property that makes mid a valid reference price.

Proof: both inequalities reduce to linear arithmetic after unfolding
the definition and clearing the denominator. Uses `linarith`
throughout; no division lemmas needed because `x / 2` is definitionally
`x * (1/2)` over ℝ and linarith handles it directly. -/
@[stat_lemma]
theorem mid_between_bid_ask {bid ask : ℝ} (h : bid ≤ ask) :
    bid ≤ midPrice bid ask ∧ midPrice bid ask ≤ ask := by
  unfold midPrice
  constructor
  · linarith
  · linarith

/-- **Mid-price lower bound.** Extracted half of `mid_between_bid_ask`
for direct use in calculations that only need the lower bound. -/
@[stat_lemma]
theorem mid_ge_bid {bid ask : ℝ} (h : bid ≤ ask) :
    bid ≤ midPrice bid ask := (mid_between_bid_ask h).1

/-- **Mid-price upper bound.** Extracted half of `mid_between_bid_ask`
for direct use in calculations that only need the upper bound. -/
@[stat_lemma]
theorem mid_le_ask {bid ask : ℝ} (h : bid ≤ ask) :
    midPrice bid ask ≤ ask := (mid_between_bid_ask h).2

/-- **Mid-price is symmetric.** Swapping bid and ask and negating
produces the same mid. More precisely, midPrice bid ask = midPrice ask bid
when they are the same value (they are — addition is commutative). -/
@[stat_lemma]
theorem mid_price_comm (bid ask : ℝ) :
    midPrice bid ask = midPrice ask bid := by
  unfold midPrice; ring

/-- **Mid-price at equality.** When bid = ask, mid = bid = ask. -/
@[stat_lemma]
theorem mid_price_at_zero_spread {p : ℝ} :
    midPrice p p = p := by
  unfold midPrice; ring

/-! ## Section 3 — Tighter Spread Means Lower Transaction Cost

The round-trip transaction cost for a market order of quantity `q` is
`spread * q`. A tighter spread (smaller `ask - bid`) directly reduces
this cost. This theorem is the mathematical foundation of the claim
that better-quoted markets reduce transaction costs for participants. -/

/-- **Round-trip transaction cost.** Buying `qty` shares at the ask
and selling them at the bid costs `spread * qty`. The cost is
non-negative when bid ≤ ask and qty ≥ 0. -/
noncomputable def roundTripCost (bid ask qty : ℝ) : ℝ :=
  spread bid ask * qty

/-- **Round-trip cost is non-negative.** For a non-negative quantity
and a non-crossed book, the round-trip cost cannot be negative.
Uses `mul_nonneg` from Mathlib: the product of two non-negative
reals is non-negative. -/
@[stat_lemma]
theorem round_trip_cost_nonneg {bid ask qty : ℝ}
    (h_book : bid ≤ ask) (h_qty : 0 ≤ qty) :
    0 ≤ roundTripCost bid ask qty := by
  unfold roundTripCost
  exact mul_nonneg (spread_nonneg h_book) h_qty

/-- **Tighter spread means lower transaction cost.** If two market
quotes have spreads `s₁ ≤ s₂` (s₁ is tighter), then for the same
non-negative quantity the cost under s₁ is at most the cost under s₂.

This is the quantitative form of "tighter quotes benefit market
participants." The proof applies `mul_le_mul_of_nonneg_right`: if
`a ≤ b` and `c ≥ 0` then `a * c ≤ b * c`. -/
@[stat_lemma]
theorem tighter_spread_lower_cost {bid₁ ask₁ bid₂ ask₂ qty : ℝ}
    (h_book₁ : bid₁ ≤ ask₁)
    (h_book₂ : bid₂ ≤ ask₂)
    (h_qty : 0 ≤ qty)
    (h_tighter : spread bid₁ ask₁ ≤ spread bid₂ ask₂) :
    roundTripCost bid₁ ask₁ qty ≤ roundTripCost bid₂ ask₂ qty := by
  unfold roundTripCost
  exact mul_le_mul_of_nonneg_right h_tighter h_qty

/-- **Spread reduction quantifies cost savings.** The savings from a
tighter spread equals the spread improvement times quantity. Formally:
`cost₂ - cost₁ = (spread₂ - spread₁) * qty ≥ 0`. -/
@[stat_lemma]
theorem spread_reduction_savings {bid₁ ask₁ bid₂ ask₂ qty : ℝ}
    (h_qty : 0 ≤ qty)
    (h_tighter : spread bid₁ ask₁ ≤ spread bid₂ ask₂) :
    0 ≤ roundTripCost bid₂ ask₂ qty - roundTripCost bid₁ ask₁ qty := by
  unfold roundTripCost
  have h_diff : 0 ≤ (spread bid₂ ask₂ - spread bid₁ ask₁) * qty :=
    mul_nonneg (by linarith) h_qty
  linarith [h_diff, mul_comm (spread bid₁ ask₁) qty,
            mul_comm (spread bid₂ ask₂) qty]

/-! ## Section 4 — Volume-Weighted Mid Price is Bounded by Bid and Ask

The volume-weighted mid price (VWMP) is a generalization of the
simple mid price. Given bid-ask pairs `(bid_i, ask_i)` with
corresponding volumes `v_i`, the VWMP weights each mid price by its
volume:

  VWMP = Σ(v_i * mid_i) / Σ(v_i)

When all individual mid prices lie in [bid_global, ask_global], the
weighted average also lies in that interval. This is a direct
consequence of the weighted-average property: a convex combination
of points in an interval stays in the interval. -/

/-- **Single-level VWMP coincides with mid.** When there is exactly
one price level, the volume-weighted mid is just the arithmetic mid.
This is the base case. -/
@[stat_lemma]
theorem vwmp_single_level_eq_mid {bid ask v : ℝ} (hv : 0 < v) :
    v * midPrice bid ask / v = midPrice bid ask := by
  field_simp

/-- **Volume-weighted mid price is bounded: upper bound.**
If each per-level mid price satisfies `mid_i ≤ ask` and volumes
`v_i ≥ 0` with total volume `V = Σv_i > 0`, then
`(Σ v_i * mid_i) / V ≤ ask`.

The proof rewrites the weighted sum, bounds each term by `v_i * ask`,
factors out the total volume, and uses `div_le_iff₀` together with
`Finset.sum_le_sum`. The key Mathlib lemmas are:
* `mul_le_mul_of_nonneg_left` (bounds each summand)
* `Finset.sum_mul` (factors the constant from the sum)
* `div_le_iff₀` (clears the denominator) -/
@[stat_lemma]
theorem vwmp_le_ask {n : ℕ} {v : Fin n → ℝ} {mid_i : Fin n → ℝ}
    {ask V : ℝ}
    (hv_nn : ∀ i, 0 ≤ v i)
    (hV_pos : 0 < V)
    (hV_sum : V = ∑ i, v i)
    (hmid_le : ∀ i, mid_i i ≤ ask) :
    (∑ i, v i * mid_i i) / V ≤ ask := by
  have hV : (0 : ℝ) < V := hV_pos
  rw [div_le_iff₀ hV]
  calc ∑ i, v i * mid_i i
      ≤ ∑ i, v i * ask := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hmid_le i) (hv_nn i)
    _ = (∑ i, v i) * ask := by rw [Finset.sum_mul]
    _ = ask * V := by rw [hV_sum]; ring

/-- **Volume-weighted mid price is bounded: lower bound.**
Symmetric to the upper bound. -/
@[stat_lemma]
theorem bid_le_vwmp {n : ℕ} {v : Fin n → ℝ} {mid_i : Fin n → ℝ}
    {bid V : ℝ}
    (hv_nn : ∀ i, 0 ≤ v i)
    (hV_pos : 0 < V)
    (hV_sum : V = ∑ i, v i)
    (hmid_ge : ∀ i, bid ≤ mid_i i) :
    bid ≤ (∑ i, v i * mid_i i) / V := by
  have hV : (0 : ℝ) < V := hV_pos
  rw [le_div_iff₀ hV]
  calc bid * V = bid * (∑ i, v i) := by rw [hV_sum]
    _ = ∑ i, bid * v i := by rw [Finset.mul_sum]
    _ = ∑ i, v i * bid := by congr 1; ext i; ring
    _ ≤ ∑ i, v i * mid_i i := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hmid_ge i) (hv_nn i)

/-- **Volume-weighted mid price lies in [bid, ask].** Combining the
upper and lower bounds: if each per-level mid price lies in
[bid, ask] and volumes are non-negative with positive total, then
the VWMP lies in [bid, ask].

This is the theorem that guarantees no VWMP-based fair-value
estimate can imply synthetic arbitrage against the quotes. -/
@[stat_lemma]
theorem vwmp_bounded_by_bid_ask {n : ℕ} {v : Fin n → ℝ} {mid_i : Fin n → ℝ}
    {bid ask V : ℝ}
    (hv_nn : ∀ i, 0 ≤ v i)
    (hV_pos : 0 < V)
    (hV_sum : V = ∑ i, v i)
    (hmid_ge : ∀ i, bid ≤ mid_i i)
    (hmid_le : ∀ i, mid_i i ≤ ask) :
    bid ≤ (∑ i, v i * mid_i i) / V ∧
    (∑ i, v i * mid_i i) / V ≤ ask :=
  ⟨bid_le_vwmp hv_nn hV_pos hV_sum hmid_ge,
   vwmp_le_ask hv_nn hV_pos hV_sum hmid_le⟩

/-- **VWMP with per-level bids and asks.** A more concrete form:
when each `mid_i = midPrice bid_i ask_i` and all quotes are within
a global [bid, ask] range, the VWMP stays in [bid, ask].

The hypothesis `hmid_in_range` captures that each arithmetic mid is
within the global range. -/
@[stat_lemma]
theorem vwmp_from_mids_bounded {n : ℕ} {v : Fin n → ℝ}
    {bid_i ask_i : Fin n → ℝ}
    {bid ask V : ℝ}
    (hv_nn : ∀ i, 0 ≤ v i)
    (hV_pos : 0 < V)
    (hV_sum : V = ∑ i, v i)
    (hbid_ge : ∀ i, bid ≤ midPrice (bid_i i) (ask_i i))
    (hask_le : ∀ i, midPrice (bid_i i) (ask_i i) ≤ ask) :
    bid ≤ (∑ i, v i * midPrice (bid_i i) (ask_i i)) / V ∧
    (∑ i, v i * midPrice (bid_i i) (ask_i i)) / V ≤ ask :=
  vwmp_bounded_by_bid_ask hv_nn hV_pos hV_sum hbid_ge hask_le

end Pythia.Finance.HFT.OrderBookProperties
