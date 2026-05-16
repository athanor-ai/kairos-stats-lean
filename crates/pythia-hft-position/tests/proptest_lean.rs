//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_hft_position::{Position, FillResult};

proptest! {
    /// Lean: `buy_increases_position`
    #[test]
    fn buy_increases(qty in 0.01f64..100.0, price in 1.0f64..1000.0) {
        let p = Position::flat(10000.0);
        if let FillResult::Filled { new_pos } = p.fill(qty, price) {
            prop_assert!(new_pos.qty > p.qty);
        }
    }

    /// Lean: `sell_decreases_position`
    #[test]
    fn sell_decreases(init_qty in 100.0f64..1000.0, sell_qty in 0.01f64..50.0, price in 1.0f64..1000.0) {
        let p = Position { qty: init_qty, avg_entry: 100.0, limit: 10000.0 };
        if let FillResult::Filled { new_pos } = p.fill(-sell_qty, price) {
            prop_assert!(new_pos.qty < p.qty);
        }
    }

    /// Lean: `within_limit` — after any accepted fill, |pos| ≤ limit
    #[test]
    fn limit_always_held(
        init in -500.0f64..500.0,
        fill in -500.0f64..500.0,
        price in 1.0f64..1000.0
    ) {
        let p = Position { qty: init, avg_entry: 100.0, limit: 1000.0 };
        match p.fill(fill, price) {
            FillResult::Filled { new_pos } => {
                prop_assert!(new_pos.qty.abs() <= new_pos.limit + 1e-10);
            }
            FillResult::Rejected => {}
        }
    }

    /// Lean: `long_profit` — positive PnL when long and mark > entry
    #[test]
    fn long_profit(qty in 1.0f64..1000.0, entry in 50.0f64..100.0, gain in 0.01f64..50.0) {
        let p = Position { qty, avg_entry: entry, limit: 10000.0 };
        prop_assert!(p.unrealized_pnl(entry + gain) > 0.0);
    }

    /// Lean: `short_profit` — positive PnL when short and mark < entry
    #[test]
    fn short_profit(qty in 1.0f64..1000.0, entry in 50.0f64..100.0, gain in 0.01f64..50.0) {
        let p = Position { qty: -qty, avg_entry: entry, limit: 10000.0 };
        prop_assert!(p.unrealized_pnl(entry - gain) > 0.0);
    }

    /// Lean: `flat_zero_risk`
    #[test]
    fn flat_zero_risk(price_change in -100.0f64..100.0) {
        let p = Position::flat(1000.0);
        prop_assert_eq!(p.market_risk(price_change), 0.0);
    }
}
