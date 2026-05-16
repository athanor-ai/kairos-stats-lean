//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_fundamentals_dcf::*;

proptest! {
    /// Lean: `pv_pos`
    #[test]
    fn pv_positive(cf in 0.01f64..10000.0, r in -0.5f64..1.0, t in 0.0f64..30.0) {
        prop_assert!(pv(cf, r, t) > 0.0);
    }

    /// Lean: `pv_antitone_rate`
    #[test]
    fn pv_antitone_rate(cf in 0.01f64..1000.0, r1 in 0.0f64..0.5, extra in 0.0f64..0.5, t in 0.0f64..20.0) {
        prop_assert!(pv(cf, r1 + extra, t) <= pv(cf, r1, t) + 1e-10);
    }

    /// Lean: `pv_antitone_time`
    #[test]
    fn pv_antitone_time(cf in 0.01f64..1000.0, r in 0.0f64..0.5, t1 in 0.0f64..10.0, extra in 0.0f64..10.0) {
        prop_assert!(pv(cf, r, t1 + extra) <= pv(cf, r, t1) + 1e-10);
    }

    /// Lean: `pv_additive`
    #[test]
    fn pv_additive(cf1 in -1000.0f64..1000.0, cf2 in -1000.0f64..1000.0, r in 0.0f64..0.5, t in 0.0f64..10.0) {
        let combined = pv(cf1 + cf2, r, t);
        let separate = pv(cf1, r, t) + pv(cf2, r, t);
        prop_assert!((combined - separate).abs() < 1e-8);
    }
}
