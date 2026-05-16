//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content.

use proptest::prelude::*;
use pythia_credit_spread::*;

proptest! {
    /// Lean: `creditSpread_nonneg` — spread nonneg when y_risky >= y_rf
    #[test]
    fn spread_nonneg(y_rf in 0.0f64..0.2, extra in 0.0f64..0.3) {
        let y_risky = y_rf + extra;
        prop_assert!(credit_spread(y_risky, y_rf) >= -1e-15);
    }

    /// Lean: `expectedLoss_nonneg` — nonneg for nonneg inputs
    #[test]
    fn el_nonneg(pd in 0.0f64..1.0, lgd in 0.0f64..1.0) {
        prop_assert!(expected_loss(pd, lgd) >= -1e-15);
    }

    /// Lean: `expectedLoss_le_lgd` — bounded by lgd when pd <= 1
    #[test]
    fn el_bounded(pd in 0.0f64..1.0, lgd in 0.0f64..1.0) {
        prop_assert!(expected_loss(pd, lgd) <= lgd + 1e-12);
    }

    /// Lean: `expectedLoss_mono_pd` — monotone in pd for fixed lgd >= 0
    #[test]
    fn el_monotone_pd(pd1 in 0.0f64..0.5, extra in 0.0f64..0.5, lgd in 0.0f64..1.0) {
        let pd2 = (pd1 + extra).min(1.0);
        prop_assert!(expected_loss(pd1, lgd) <= expected_loss(pd2, lgd) + 1e-12);
    }
}
