//! Property tests derived from Lean theorems in
//! Pythia.Finance.HFT.OrderBook + OrderBookStrong.

use proptest::prelude::*;
use pythia_hft_orderbook::{OrderBook, Side};

// Lean theorem: bidSorted (OrderBook.lean)
// After any sequence of inserts, bids remain sorted by price-time priority.
proptest! {
    #[test]
    fn bid_sorted_after_inserts(
        prices in prop::collection::vec(1i64..1000, 1..20),
    ) {
        let mut book = OrderBook::new(1);
        for (i, &price) in prices.iter().enumerate() {
            book.insert(i as u64, price, 10, Side::Bid);
        }
        prop_assert!(book.is_bid_sorted(),
            "bid_sorted violated after {} inserts", prices.len());
    }
}

// Lean theorem: ask sorted (symmetric)
proptest! {
    #[test]
    fn ask_sorted_after_inserts(
        prices in prop::collection::vec(1i64..1000, 1..20),
    ) {
        let mut book = OrderBook::new(1);
        for (i, &price) in prices.iter().enumerate() {
            book.insert(i as u64, price, 10, Side::Ask);
        }
        prop_assert!(book.is_ask_sorted(),
            "ask_sorted violated after {} inserts", prices.len());
    }
}

// Lean theorem: no_cross (OrderBook.lean)
// After matching, best_bid < best_ask (book is not crossed).
proptest! {
    #[test]
    fn no_cross_after_operations(
        ops in prop::collection::vec(
            (1i64..100, 1u64..50, prop::bool::ANY),
            1..30
        ),
    ) {
        let mut book = OrderBook::new(1);
        for (i, &(price, qty, is_bid)) in ops.iter().enumerate() {
            let side = if is_bid { Side::Bid } else { Side::Ask };
            book.insert(i as u64, price, qty, side);
        }
        prop_assert!(book.is_uncrossed(),
            "no_cross violated: best_bid={:?}, best_ask={:?}",
            book.best_bid(), book.best_ask());
    }
}

// Lean theorem: spread_nonneg (OrderBook.lean)
// Spread is always >= 0 when both sides have orders.
proptest! {
    #[test]
    fn spread_nonneg(
        bid_price in 1i64..500,
        ask_price in 501i64..1000,
    ) {
        let mut book = OrderBook::new(1);
        book.insert(0, bid_price, 10, Side::Bid);
        book.insert(1, ask_price, 10, Side::Ask);
        if let Some(spread) = book.spread() {
            prop_assert!(spread >= 0,
                "spread_nonneg violated: spread={}", spread);
        }
    }
}

// Lean theorem: tick_size_gap (OrderBook.lean)
// All prices on the book are multiples of tick_size.
// Spread >= tick_size when both sides have orders.
proptest! {
    #[test]
    fn tick_aligned_prices(
        bid_ticks in 1i64..100,
        ask_ticks in 101i64..200,
        tick_size in 1i64..10,
    ) {
        let mut book = OrderBook::new(tick_size);
        let bid_price = bid_ticks * tick_size;
        let ask_price = ask_ticks * tick_size;
        book.insert(0, bid_price, 10, Side::Bid);
        book.insert(1, ask_price, 10, Side::Ask);
        if let Some(spread) = book.spread() {
            prop_assert!(spread >= tick_size,
                "tick_aligned_spread violated: spread={}, tick={}",
                spread, tick_size);
        }
    }
}

// Lean theorem: fifo_at_price (OrderBook.lean)
// Orders at the same price are filled in arrival order.
proptest! {
    #[test]
    fn fifo_within_price_level(
        n_orders in 2usize..10,
    ) {
        let mut book = OrderBook::new(1);
        let price = 100;
        for i in 0..n_orders {
            book.insert(i as u64, price, 10, Side::Ask);
        }
        // Aggressive bid should fill order 0 first (lowest seqno)
        let fills = book.insert(100, price, 10, Side::Bid);
        prop_assert_eq!(fills.len(), 1);
        prop_assert_eq!(fills[0].maker_id, 0,
            "FIFO violated: filled order {} instead of 0", fills[0].maker_id);
    }
}

// Lean theorem: cancel preserves sorting
proptest! {
    #[test]
    fn cancel_preserves_sorted(
        prices in prop::collection::vec(1i64..1000, 2..15),
        cancel_idx in 0usize..14,
    ) {
        let mut book = OrderBook::new(1);
        for (i, &price) in prices.iter().enumerate() {
            book.insert(i as u64, price, 10, Side::Bid);
        }
        let cancel_id = cancel_idx.min(prices.len() - 1) as u64;
        book.cancel(cancel_id);
        prop_assert!(book.is_bid_sorted(),
            "sorted invariant violated after cancel");
    }
}
