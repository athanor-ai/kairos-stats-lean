//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property corresponds to a Lean theorem in
//! Pythia.Finance.HFT.OrderBookProperties using Finset reasoning
//! (sum_union, filter_subset, max'/min', card_cons, sum_erase_eq_sub,
//! disjoint_left + lt_irrefl).

use proptest::prelude::*;
use pythia_hft_orderbook_props::{Fill, OrderBook, Side, vwap};

// Lean theorem: `volume_additive`
// (bids ∪ asks).sum qty = bids.sum qty + asks.sum qty
proptest! {
    #[test]
    fn volume_additive(
        bid_qtys in prop::collection::vec(1u64..1000, 1..20),
        ask_qtys in prop::collection::vec(1u64..1000, 1..20),
    ) {
        let mut book = OrderBook::new();
        for (i, &qty) in bid_qtys.iter().enumerate() {
            book.insert(100 + i as i64, qty, Side::Bid);
        }
        for (i, &qty) in ask_qtys.iter().enumerate() {
            book.insert(200 + i as i64, qty, Side::Ask);
        }
        let bid_vol = book.total_volume(Side::Bid);
        let ask_vol = book.total_volume(Side::Ask);
        prop_assert_eq!(book.total_volume_both_sides(), bid_vol + ask_vol,
            "volume_additive violated");
    }
}

// Lean theorem: `best_bid_is_max`
// ∀ p ∈ bids, p ≤ max' bids
proptest! {
    #[test]
    fn best_bid_is_maximum(
        prices in prop::collection::vec(1i64..10000, 1..30),
    ) {
        let mut book = OrderBook::new();
        for (i, &price) in prices.iter().enumerate() {
            book.insert(price, 10, Side::Bid);
            let _ = i;
        }
        let best = book.best_bid().unwrap();
        let max_price = *prices.iter().max().unwrap();
        prop_assert_eq!(best, max_price,
            "best_bid_is_max violated: best={}, max={}", best, max_price);
    }
}

// Lean theorem: `best_ask_is_min`
// ∀ p ∈ asks, min' asks ≤ p
proptest! {
    #[test]
    fn best_ask_is_minimum(
        prices in prop::collection::vec(1i64..10000, 1..30),
    ) {
        let mut book = OrderBook::new();
        for &price in &prices {
            book.insert(price, 10, Side::Ask);
        }
        let best = book.best_ask().unwrap();
        let min_price = *prices.iter().min().unwrap();
        prop_assert_eq!(best, min_price,
            "best_ask_is_min violated: best={}, min={}", best, min_price);
    }
}

// Lean theorem: `spread_positive_implies_disjoint`
// ∀ b ∈ bids, ∀ a ∈ asks, b < a ⇒ Disjoint bids asks
proptest! {
    #[test]
    fn spread_positive_implies_disjoint(
        bid_prices in prop::collection::vec(1i64..100, 1..10),
        ask_offset in 1i64..50,
    ) {
        let mut book = OrderBook::new();
        let max_bid = *bid_prices.iter().max().unwrap();
        for &bp in &bid_prices {
            book.insert(bp, 10, Side::Bid);
        }
        // All asks strictly above max bid
        for i in 0..5 {
            book.insert(max_bid + ask_offset + i, 10, Side::Ask);
        }
        prop_assert!(book.price_sets_disjoint(),
            "spread_positive_implies_disjoint violated");
        prop_assert!(book.is_uncrossed(),
            "book crossed despite positive spread");
    }
}

// Lean theorem: `cancel_reduces_volume`
// (orders.erase o).sum qty = orders.sum qty - o.qty
proptest! {
    #[test]
    fn cancel_reduces_volume(
        qtys in prop::collection::vec(1u64..500, 2..15),
        cancel_idx in 0usize..14,
    ) {
        let mut book = OrderBook::new();
        let mut ids = Vec::new();
        for &qty in &qtys {
            ids.push(book.insert(100, qty, Side::Bid));
        }
        let idx = cancel_idx % qtys.len();
        let vol_before = book.total_volume(Side::Bid);
        let cancelled_qty = book.cancel(ids[idx]).unwrap();
        let vol_after = book.total_volume(Side::Bid);
        prop_assert_eq!(vol_after, vol_before - cancelled_qty,
            "cancel_reduces_volume violated");
    }
}

// Lean theorem: `vwap_between_extremes`
// min_price ≤ vwap ≤ max_price
proptest! {
    #[test]
    fn vwap_between_extremes(
        fill_data in prop::collection::vec((1i64..1000, 1u64..100), 1..20),
    ) {
        let fills: Vec<Fill> = fill_data.iter().enumerate().map(|(i, &(price, qty))| {
            Fill { price, qty, maker_id: i as u64, taker_id: 999 }
        }).collect();
        if let Some(v) = vwap(&fills) {
            let min_price = fills.iter().map(|f| f.price).min().unwrap() as f64;
            let max_price = fills.iter().map(|f| f.price).max().unwrap() as f64;
            prop_assert!(v >= min_price - 1e-10,
                "vwap {} < min_price {}", v, min_price);
            prop_assert!(v <= max_price + 1e-10,
                "vwap {} > max_price {}", v, max_price);
        }
    }
}
