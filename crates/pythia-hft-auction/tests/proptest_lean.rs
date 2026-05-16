//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_hft_auction::{AuctionOrder, run_auction};

proptest! {
    /// Lean: `clearing_price_bounded` + `buyer_surplus_nonneg` + `seller_surplus_nonneg`
    #[test]
    fn auction_invariants(
        bid_price in 100.0f64..110.0,
        ask_price in 90.0f64..100.0,
        qty in 1.0f64..1000.0
    ) {
        let orders = vec![
            AuctionOrder { limit_price: bid_price, qty, is_buy: true },
            AuctionOrder { limit_price: ask_price, qty, is_buy: false },
        ];
        if let Some(result) = run_auction(&orders) {
            prop_assert!(result.price_bounded(ask_price, bid_price));
            prop_assert!(result.buyer_surplus(bid_price) >= -1e-10);
            prop_assert!(result.seller_surplus(ask_price) >= -1e-10);
        }
    }
}
