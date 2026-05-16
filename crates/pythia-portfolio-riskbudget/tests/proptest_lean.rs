//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_riskbudget::*;

proptest! {
    /// Lean: `euler_sum`
    #[test]
    fn euler_sums(m1 in 0.0f64..10.0, m2 in 0.0f64..10.0, m3 in 0.0f64..10.0) {
        let total = m1 + m2 + m3;
        prop_assert!(euler_check(&[m1, m2, m3], total, 1e-10));
    }

    /// Lean: `contribution_le_total`
    #[test]
    fn mcr_bounded(m1 in 0.0f64..10.0, m2 in 0.0f64..10.0) {
        let total = m1 + m2;
        prop_assert!(pythia_portfolio_riskbudget::contribution_bounded(&[m1, m2], total));
    }

    /// Lean: `risk_hhi_nonneg`
    #[test]
    fn hhi_nonneg(s1 in -1.0f64..1.0, s2 in -1.0f64..1.0, s3 in -1.0f64..1.0) {
        prop_assert!(risk_hhi(&[s1, s2, s3]) >= 0.0);
    }

    /// Lean: `equal_risk_contribution`
    #[test]
    fn equal_risk_sums(total in 0.1f64..100.0, n in 1usize..20) {
        let target = equal_risk_target(total, n);
        let sum = target * n as f64;
        prop_assert!((sum - total).abs() < 1e-8);
    }
}
