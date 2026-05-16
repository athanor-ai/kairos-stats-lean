//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_risk_vol::*;

proptest! {
    /// Lean: `ewma_nonneg`
    #[test]
    fn ewma_nonneg(lam in 0.0f64..1.0, s in 0.0f64..0.1, r in 0.0f64..0.1) {
        prop_assert!(ewma(lam, s, r) >= -1e-15);
    }

    /// Lean: `ewma_between` — convex combination
    #[test]
    fn ewma_between(lam in 0.0f64..1.0, s in 0.0f64..0.05, extra in 0.0f64..0.05) {
        let r = s + extra;
        let e = ewma(lam, s, r);
        prop_assert!(e >= s - 1e-12);
        prop_assert!(e <= r + 1e-12);
    }

    /// Lean: `garch_unconditional_pos`
    #[test]
    fn garch_pos(omega in 0.001f64..0.01, alpha in 0.01f64..0.1, beta in 0.5f64..0.85) {
        if alpha + beta < 1.0 {
            prop_assert!(garch_unconditional(omega, alpha, beta) > 0.0);
        }
    }

    /// Lean: `garch_stationarity_condition`
    #[test]
    fn stationarity(alpha in 0.0f64..0.5, beta in 0.0f64..0.5) {
        if alpha + beta < 1.0 {
            prop_assert!(is_stationary(alpha, beta));
        }
    }
}
