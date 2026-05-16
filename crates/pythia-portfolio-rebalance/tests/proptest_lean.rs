//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_rebalance::*;

proptest! {
    /// Lean: `tradeFraction_zero_iff`
    #[test]
    fn trade_fraction_zero_iff(w in 0.0f64..1.0) {
        prop_assert!((trade_fraction(w, w)).abs() < 1e-15);
    }

    /// Lean: `tradeFraction_antisymm`
    #[test]
    fn trade_fraction_antisymm(w_t in 0.0f64..1.0, w_c in 0.0f64..1.0) {
        let tf1 = trade_fraction(w_t, w_c);
        let tf2 = trade_fraction(w_c, w_t);
        prop_assert!((tf1 + tf2).abs() < 1e-10);
    }

    /// Lean: `driftedWealth_at_equal_returns`
    #[test]
    fn drifted_wealth_equal_returns(w in 0.0f64..1.0, r in -0.9f64..2.0) {
        let dw = drifted_wealth(w, r, r);
        prop_assert!((dw - (1.0 + r)).abs() < 1e-10);
    }

    /// Lean: `driftedWealth_pos`
    #[test]
    fn drifted_wealth_positive(w in 0.0f64..1.0, r1 in -0.99f64..2.0, r2 in -0.99f64..2.0) {
        prop_assert!(drifted_wealth(w, r1, r2) > 0.0);
    }
}
