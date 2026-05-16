//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_risk_leverage::*;

proptest! {
    /// Lean: `leverageDrag_identity`
    #[test]
    fn drag_identity(l in 1.0f64..5.0, r1 in -0.2f64..0.2, r2 in -0.2f64..0.2) {
        let lhs = compound_two_period(leveraged_return(l, r1), leveraged_return(l, r2))
            - leveraged_return(l, compound_two_period(r1, r2));
        let rhs = leverage_drag(l, r1, r2);
        prop_assert!((lhs - rhs).abs() < 1e-10);
    }

    /// Lean: `leverageDrag_nonneg_of_same_sign`
    #[test]
    fn drag_nonneg_same_sign(l in 1.0f64..10.0, r1 in 0.0f64..0.3, r2 in 0.0f64..0.3) {
        prop_assert!(leverage_drag(l, r1, r2) >= 0.0);
    }

    /// Lean: `compoundTwoPeriod_comm`
    #[test]
    fn compound_comm(r1 in -0.5f64..1.0, r2 in -0.5f64..1.0) {
        let a = compound_two_period(r1, r2);
        let b = compound_two_period(r2, r1);
        prop_assert!((a - b).abs() < 1e-10);
    }

    /// Lean: `leverageDrag_abs_mono_L`
    #[test]
    fn drag_mono_leverage(l1 in 1.0f64..5.0, extra in 0.0f64..5.0, r1 in 0.0f64..0.2, r2 in 0.0f64..0.2) {
        let l2 = l1 + extra;
        prop_assert!(leverage_drag(l1, r1, r2) <= leverage_drag(l2, r1, r2) + 1e-10);
    }
}
