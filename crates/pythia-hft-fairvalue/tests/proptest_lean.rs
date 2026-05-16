//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_hft_fairvalue::{micro_price, ewma_update};

proptest! {
    /// Lean: `microPrice_between` — micro-price between bid and ask
    #[test]
    fn micro_between(bid in 90.0f64..100.0, spread in 0.01f64..5.0, bq in 1.0f64..1000.0, aq in 1.0f64..1000.0) {
        let ask = bid + spread;
        let m = micro_price(bid, ask, bq, aq);
        prop_assert!(m >= bid - 1e-10, "micro {} < bid {}", m, bid);
        prop_assert!(m <= ask + 1e-10, "micro {} > ask {}", m, ask);
    }

    /// Lean: `microPrice_equal_sizes` — equal qty → true mid
    #[test]
    fn equal_sizes_mid(bid in 90.0f64..100.0, spread in 0.01f64..5.0, qty in 1.0f64..1000.0) {
        let ask = bid + spread;
        let m = micro_price(bid, ask, qty, qty);
        let mid = (bid + ask) / 2.0;
        prop_assert!((m - mid).abs() < 1e-10);
    }

    /// Lean: `microPrice_shifts_toward_thin` — more ask_qty shifts toward bid
    #[test]
    fn imbalance_shifts(bid in 90.0f64..100.0, spread in 0.1f64..5.0, bq in 1.0f64..100.0, extra in 1.0f64..900.0) {
        let ask = bid + spread;
        let aq = bq + extra;
        let m = micro_price(bid, ask, bq, aq);
        let mid = (bid + ask) / 2.0;
        prop_assert!(m < mid + 1e-10);
    }

    /// Lean: `ewma_between` — EWMA is between old and trade when alpha in [0,1] and old ≤ trade
    #[test]
    fn ewma_between(alpha in 0.0f64..=1.0, old in 90.0f64..100.0, gain in 0.0f64..20.0) {
        let trade = old + gain;
        let new_val = ewma_update(alpha, trade, old);
        prop_assert!(new_val >= old - 1e-10);
        prop_assert!(new_val <= trade + 1e-10);
    }
}
