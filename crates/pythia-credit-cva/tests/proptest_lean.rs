//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_credit_cva::*;

proptest! {
    /// Lean: `cva_nonneg`
    #[test]
    fn cva_nonneg(lgd in 0.0f64..1.0, e1 in 0.0f64..1000.0, e2 in 0.0f64..1000.0, d1 in 0.0f64..0.1, d2 in 0.0f64..0.1) {
        prop_assert!(cva(lgd, &[e1, e2], &[d1, d2]) >= -1e-12);
    }

    /// Lean: `cva_mono_lgd`
    #[test]
    fn cva_mono_lgd(lgd1 in 0.0f64..0.5, extra in 0.0f64..0.5, e1 in 0.0f64..500.0, d1 in 0.0f64..0.05) {
        let lgd2 = lgd1 + extra;
        prop_assert!(cva(lgd1, &[e1], &[d1]) <= cva(lgd2, &[e1], &[d1]) + 1e-12);
    }

    /// Lean: `netting_reduces_cva`
    #[test]
    fn netting_benefit_nonneg(netted in 0.0f64..50.0, standalone in 50.0f64..100.0) {
        prop_assert!(netting_benefit(netted, standalone) >= -1e-12);
    }

    /// Lean: `bilateral_cva`
    #[test]
    fn bilateral_decomposition(cva_val in 0.0f64..100.0, dva in 0.0f64..50.0) {
        let bcva = bilateral_cva(cva_val, dva);
        prop_assert!((bcva - (cva_val - dva)).abs() < 1e-10);
    }
}
