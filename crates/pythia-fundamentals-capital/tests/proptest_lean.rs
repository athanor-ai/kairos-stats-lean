//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_fundamentals_capital::*;

proptest! {
    /// Lean: `tax_shield_nonneg`
    #[test]
    fn tax_shield_nonneg_prop(tax_rate in 0.0f64..1.0, debt in 0.0f64..1e7) {
        prop_assert!(check_tax_shield_nonneg(tax_rate, debt));
    }

    /// Lean: `wacc_tax_benefit`
    #[test]
    fn wacc_tax_benefit_prop(rd in 0.0f64..0.2, tax_rate in 0.0f64..1.0) {
        prop_assert!(check_wacc_tax_benefit(rd, tax_rate));
    }

    /// Lean: `leverage_amplifies_vol`
    #[test]
    fn leverage_amplifies_prop(sigma_a in 0.0f64..1.0, d_over_e in 0.0f64..10.0) {
        prop_assert!(check_leverage_amplifies(sigma_a, d_over_e));
    }

    /// Lean: `coverage_adequate`
    #[test]
    fn coverage_adequate_prop(interest in 0.01f64..1e6, extra in 0.0f64..1e6) {
        prop_assert!(check_coverage_adequate(interest + extra, interest));
    }
}
