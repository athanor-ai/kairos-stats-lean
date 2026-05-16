//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_options_american::*;

proptest! {
    /// Lean: `early_exercise_premium_nonneg`
    #[test]
    fn premium_nonneg(v_eu in 0.0f64..100.0, premium in 0.0f64..20.0) {
        let v_am = v_eu + premium;
        prop_assert!(early_exercise_premium(v_am, v_eu) >= -1e-12);
    }

    /// Lean: `american_ge_european`
    #[test]
    fn am_ge_eu(v_eu in 0.0f64..100.0, premium in 0.0f64..20.0) {
        let v_am = v_eu + premium;
        prop_assert!(check_american_ge_european(v_am, v_eu));
    }

    /// Lean: `american_ge_intrinsic`
    #[test]
    fn am_ge_intrinsic(intrinsic in 0.0f64..50.0, time_value in 0.0f64..20.0) {
        let v_am = intrinsic + time_value;
        prop_assert!(check_american_ge_intrinsic(v_am, intrinsic));
    }

    /// Lean: `put_early_exercise_value`
    #[test]
    fn put_exercise_pos(intrinsic in 1.0f64..100.0, discount in 0.01f64..0.5) {
        let pv = intrinsic * (1.0 - discount);
        prop_assert!(put_early_exercise_value(intrinsic, pv) > 0.0);
    }
}
