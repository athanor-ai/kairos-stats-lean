//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_tca::*;

proptest! {
    /// `implementation_shortfall_nonneg`: IS >= 0 for adverse execution (exec >= decision).
    #[test]
    fn prop_implementation_shortfall_nonneg(
        decision in 1.0f64..1000.0,
        markup in 0.0f64..100.0,
    ) {
        let exec = decision + markup;
        let is = implementation_shortfall(decision, exec);
        prop_assert!(is >= -1e-12,
            "implementation_shortfall_nonneg violated: IS = {}", is);
    }

    /// `impact_grows_with_size`: market impact is monotone in order size for eta >= 0.
    #[test]
    fn prop_impact_grows_with_size(
        eta in 0.0f64..0.01,
        q1 in 0.0f64..100000.0,
        delta in 0.0f64..100000.0,
    ) {
        let q2 = q1 + delta;
        let i1 = market_impact(eta, q1);
        let i2 = market_impact(eta, q2);
        prop_assert!(i1 <= i2 + 1e-12,
            "impact_grows_with_size violated: impact({}) = {} > impact({}) = {}", q1, i1, q2, i2);
    }

    /// `total_cost_nonneg`: total trading cost >= 0 when all components >= 0.
    #[test]
    fn prop_total_cost_nonneg(
        commission in 0.0f64..100.0,
        spread in 0.0f64..1.0,
        impact in 0.0f64..10.0,
        timing in 0.0f64..5.0,
    ) {
        let tc = total_trading_cost(commission, spread, impact, timing);
        prop_assert!(tc >= -1e-12,
            "total_cost_nonneg violated: tc = {}", tc);
    }

    /// `is_decomposition`: total always equals delay + impact + timing.
    #[test]
    fn prop_is_decomposition(
        delay in -10.0f64..10.0,
        impact in -10.0f64..10.0,
        timing in -10.0f64..10.0,
    ) {
        let decomp = IsDecomposition::new(delay, impact, timing);
        let total = decomp.total();
        let expected = delay + impact + timing;
        prop_assert!((total - expected).abs() < 1e-12,
            "is_decomposition violated: {} != {}", total, expected);
    }
}
