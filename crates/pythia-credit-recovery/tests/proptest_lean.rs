//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_credit_recovery::*;

proptest! {
    /// Lean: `lgd_complement` — LGD in [0,1]
    #[test]
    fn lgd_bounded(r in 0.0f64..1.0) {
        let l = lgd(r);
        prop_assert!(l >= -1e-15);
        prop_assert!(l <= 1.0 + 1e-15);
    }

    /// Lean: `lgd_antitone_recovery`
    #[test]
    fn lgd_antitone(r1 in 0.0f64..0.5, extra in 0.0f64..0.5) {
        let r2 = r1 + extra;
        prop_assert!(lgd(r2) <= lgd(r1) + 1e-12);
    }

    /// Lean: `expected_loss_nonneg`
    #[test]
    fn el_nonneg(pd in 0.0f64..1.0, r in 0.0f64..1.0) {
        prop_assert!(expected_loss(pd, r) >= -1e-15);
    }

    /// Lean: `expected_loss_le_pd`
    #[test]
    fn el_le_pd(pd in 0.0f64..1.0, r in 0.0f64..1.0) {
        prop_assert!(expected_loss(pd, r) <= pd + 1e-12);
    }
}
