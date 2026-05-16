//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_leverage::*;

proptest! {
    /// Lean: `gross_ge_abs_net` — triangle inequality
    #[test]
    fn gross_ge_abs_net(w1 in -2.0f64..2.0, w2 in -2.0f64..2.0, w3 in -2.0f64..2.0) {
        let w = &[w1, w2, w3];
        prop_assert!(gross_leverage(w) >= net_leverage(w).abs() - 1e-10);
    }

    /// Lean: `gross_leverage_nonneg`
    #[test]
    fn gross_nonneg(w1 in -5.0f64..5.0, w2 in -5.0f64..5.0) {
        prop_assert!(gross_leverage(&[w1, w2]) >= 0.0);
    }

    /// Lean: `leverage_within_limit`
    #[test]
    fn within_limit_check(gross in 0.0f64..500.0, equity in 50.0f64..200.0, limit in 1.0f64..10.0) {
        if gross <= limit * equity {
            prop_assert!(within_limit(gross, equity, limit));
        }
    }

    /// Lean: `margin_nonneg`
    #[test]
    fn margin_nonneg(m in 0.0f64..1.0, v in -10000.0f64..10000.0) {
        prop_assert!(margin_required(m, v) >= -1e-15);
    }
}
