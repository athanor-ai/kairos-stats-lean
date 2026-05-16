//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (le_max_right, max_eq_right/left, sub_nonpos, sub_nonneg, max_le_max_right, ring).

use proptest::prelude::*;
use pythia_options_time_premium::*;

proptest! {
    /// Lean: `intrinsicValue_nonneg` — le_max_right
    #[test]
    fn intrinsic_nonneg(s in 0.0f64..200.0, k in 0.0f64..200.0) {
        prop_assert!(intrinsic_value(s, k) >= 0.0);
    }

    /// Lean: `intrinsicValue_zero_otm` — max_eq_right (sub_nonpos.mpr h)
    #[test]
    fn intrinsic_zero_otm(k in 50.0f64..200.0, below in 0.0f64..50.0) {
        let s = k - below;  // s <= k
        prop_assert!((intrinsic_value(s, k) - 0.0).abs() < 1e-10);
    }

    /// Lean: `intrinsicValue_mono_spot` — max_le_max_right + sub_le_sub_right
    #[test]
    fn intrinsic_mono_spot(s1 in 0.0f64..150.0, extra in 0.0f64..50.0, k in 0.0f64..200.0) {
        prop_assert!(intrinsic_value(s1, k) <= intrinsic_value(s1 + extra, k) + 1e-10);
    }

    /// Lean: `timePremium_nonneg_of_price_ge_intrinsic` — sub_nonneg.mpr
    #[test]
    fn time_premium_nonneg(s in 50.0f64..200.0, k in 50.0f64..200.0, excess in 0.0f64..50.0) {
        let iv = intrinsic_value(s, k);
        let c = iv + excess;  // c >= intrinsic by construction
        prop_assert!(time_premium(c, s, k) >= -1e-10);
    }
}
