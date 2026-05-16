//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_finance_backtest::*;

proptest! {
    /// Lean: `bonferroni_antitone` — more strategies → stricter threshold
    #[test]
    fn bonferroni_antitone(alpha in 0.001f64..0.1, n1 in 1usize..50, extra in 1usize..50) {
        let n2 = n1 + extra;
        prop_assert!(bonferroni_threshold(alpha, n2) <= bonferroni_threshold(alpha, n1) + 1e-15);
    }

    /// Lean: `bonferroni_threshold_pos`
    #[test]
    fn bonferroni_pos(alpha in 0.001f64..0.1, n in 1usize..1000) {
        prop_assert!(bonferroni_threshold(alpha, n) > 0.0);
    }

    /// Lean: `deflation_adjustment_nonneg` — DSR ≤ observed
    #[test]
    fn deflated_below_observed(sharpe in 0.1f64..5.0, n in 2usize..1000, vol in 0.0f64..1.0) {
        let dsr = deflated_sharpe(sharpe, n, vol);
        prop_assert!(dsr <= sharpe + 1e-10);
    }

    /// Lean: `overfit_penalty_expected`
    #[test]
    fn overfit_penalty_nonneg(sharpe_is in 0.5f64..3.0, degradation in 0.0f64..1.0) {
        let sharpe_oos = sharpe_is - degradation;
        prop_assert!(overfit_penalty(sharpe_is, sharpe_oos) >= -1e-10);
    }
}
