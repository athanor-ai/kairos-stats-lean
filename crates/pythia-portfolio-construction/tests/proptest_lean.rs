//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

//! Property tests for portfolio construction, mirroring Lean spec
//! `Pythia.Finance.Portfolio.PortfolioConstruction`.

use proptest::prelude::*;
use pythia_portfolio_construction::{turnover, rebalancing_cost, Portfolio};

/// Generate a long-only portfolio with `n` assets summing to 1.
fn arb_long_only_portfolio(n: usize) -> impl Strategy<Value = Portfolio> {
    // Generate n positive floats, then normalise to sum to 1.
    proptest::collection::vec(0.01f64..1.0, n).prop_map(|raw| {
        let total: f64 = raw.iter().sum();
        Portfolio::new(raw.into_iter().map(|w| w / total).collect())
    })
}

proptest! {
    /// Lean: `turnover_nonneg` -- turnover is always nonneg.
    #[test]
    fn prop_turnover_nonneg(
        old in arb_long_only_portfolio(5),
        new in arb_long_only_portfolio(5),
    ) {
        prop_assert!(turnover(&old, &new) >= 0.0);
    }

    /// Lean: `turnover_le_two` -- for long-only portfolios summing to 1,
    /// turnover <= 2.
    #[test]
    fn prop_turnover_le_two(
        old in arb_long_only_portfolio(5),
        new in arb_long_only_portfolio(5),
    ) {
        let t = turnover(&old, &new);
        prop_assert!(t <= 2.0 + 1e-10, "turnover {} > 2", t);
    }

    /// Lean: `rebalancing_cost_nonneg` -- cost_rate >= 0 implies cost >= 0.
    #[test]
    fn prop_rebalancing_cost_nonneg(
        old in arb_long_only_portfolio(5),
        new in arb_long_only_portfolio(5),
        cost_rate in 0.0f64..0.05,
    ) {
        let cost = rebalancing_cost(cost_rate, &old, &new);
        prop_assert!(cost >= 0.0, "cost {} < 0", cost);
    }

    /// Lean: `zero_turnover_iff_unchanged` -- identical portfolios have zero turnover.
    #[test]
    fn prop_zero_turnover_self(p in arb_long_only_portfolio(5)) {
        let t = turnover(&p, &p);
        prop_assert!(t.abs() < 1e-14, "self-turnover {} != 0", t);
    }
}
