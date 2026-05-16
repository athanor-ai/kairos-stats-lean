//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_risk_correlation::*;

proptest! {
    /// Lean: `uncorrelated_reduces_var` — zero corr < perfect corr
    #[test]
    fn zero_less_than_perfect(w1 in 0.01f64..1.0, v1 in 0.001f64..0.1, w2 in 0.01f64..1.0, v2 in 0.001f64..0.1) {
        let v_perf = portfolio_variance(w1, v1, w2, v2, 1.0);
        let v_zero = portfolio_variance(w1, v1, w2, v2, 0.0);
        prop_assert!(v_zero <= v_perf + 1e-10);
    }

    /// Lean: `negative_corr_reduces_more`
    #[test]
    fn negative_less_than_zero(w1 in 0.01f64..1.0, v1 in 0.001f64..0.1, w2 in 0.01f64..1.0, v2 in 0.001f64..0.1, neg_rho in -1.0f64..0.0) {
        let v_zero = portfolio_variance(w1, v1, w2, v2, 0.0);
        let v_neg = portfolio_variance(w1, v1, w2, v2, neg_rho);
        prop_assert!(v_neg <= v_zero + 1e-10);
    }

    /// Lean: `stress_increases_var` — higher corr = higher var
    #[test]
    fn stress_increases(w1 in 0.01f64..1.0, v1 in 0.001f64..0.1, w2 in 0.01f64..1.0, v2 in 0.001f64..0.1, rho1 in -0.5f64..0.5, extra in 0.0f64..0.5) {
        let rho2 = (rho1 + extra).min(1.0);
        let inc = stress_var_increase(w1, v1, w2, v2, rho1, rho2);
        prop_assert!(inc >= -1e-10);
    }

    /// Lean: `correlation_bounded`
    #[test]
    fn valid_corr(rho in -1.0f64..=1.0) {
        prop_assert!(is_valid_correlation(rho));
    }
}
