//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_fundamentals_gordon::*;

proptest! {
    /// Lean: `gordonGrowthPrice_zero_growth`
    #[test]
    fn zero_growth_is_perpetuity(d1 in 0.01f64..1000.0, r in 0.01f64..1.0) {
        let price = gordon_price(d1, r, 0.0);
        let perp = d1 / r;
        prop_assert!((price - perp).abs() < 1e-8);
    }

    /// Lean: `gordonGrowthPrice_linear_D`
    #[test]
    fn linear_in_dividend(d1 in 0.01f64..500.0, dd in -100.0f64..500.0, r in 0.05f64..0.5, g in 0.0f64..0.04) {
        let combined = gordon_price(d1 + dd, r, g);
        let separate = gordon_price(d1, r, g) + dd / (r - g);
        prop_assert!((combined - separate).abs() < 1e-8);
    }

    /// Lean: `gordonGrowthPrice_scale_D`
    #[test]
    fn scale_invariance(d1 in 0.01f64..500.0, alpha in -10.0f64..10.0, r in 0.05f64..0.5, g in 0.0f64..0.04) {
        let scaled = gordon_price(alpha * d1, r, g);
        let expected = alpha * gordon_price(d1, r, g);
        prop_assert!((scaled - expected).abs() < 1e-8);
    }
}
