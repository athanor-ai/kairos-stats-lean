//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content.

use proptest::prelude::*;
use pythia_fixedincome_bond::*;

proptest! {
    /// Lean: `bondPrice_pos` — positive face value implies positive price
    #[test]
    fn price_positive(fv in 0.01f64..10000.0, y in -0.1f64..0.5, t in 0.0f64..30.0) {
        prop_assert!(bond_price(fv, y, t) > 0.0);
    }

    /// Lean: `bondPrice_zero_maturity` — zero maturity gives face value
    #[test]
    fn zero_maturity(fv in 0.01f64..10000.0, y in -0.1f64..0.5) {
        let p = bond_price(fv, y, 0.0);
        prop_assert!((p - fv).abs() < 1e-10);
    }

    /// Lean: `bondPrice_antitone_yield` — higher yield, lower price (FV > 0, T >= 0)
    #[test]
    fn antitone_yield(fv in 0.01f64..10000.0, t in 0.0f64..30.0, y1 in 0.0f64..0.2, extra in 0.0f64..0.3) {
        let y2 = y1 + extra;
        prop_assert!(bond_price(fv, y2, t) <= bond_price(fv, y1, t) + 1e-10);
    }

    /// Lean: `bondPrice_mono_face` — higher face value, higher price
    #[test]
    fn mono_face(y in 0.0f64..0.3, t in 0.0f64..30.0, fv1 in 0.01f64..5000.0, extra in 0.0f64..5000.0) {
        let fv2 = fv1 + extra;
        prop_assert!(bond_price(fv1, y, t) <= bond_price(fv2, y, t) + 1e-10);
    }
}
