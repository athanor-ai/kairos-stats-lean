//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (case splits, max reasoning, mul_le_mul, linarith).

use proptest::prelude::*;
use pythia_options_bounds::*;

proptest! {
    /// Lean: `callIntrinsic_nonneg` — le_max_right
    #[test]
    fn intrinsic_nonneg(s in 50.0f64..200.0, k in 50.0f64..200.0, d in 0.5f64..1.0) {
        prop_assert!(call_intrinsic(s, k, d) >= 0.0);
    }

    /// Lean: `callIntrinsic_mono_spot` — max_le_max_right + sub_le_sub_right
    #[test]
    fn mono_spot(s1 in 50.0f64..150.0, extra in 0.0f64..50.0, k in 50.0f64..150.0, d in 0.5f64..1.0) {
        prop_assert!(call_intrinsic(s1, k, d) <= call_intrinsic(s1 + extra, k, d) + 1e-10);
    }

    /// Lean: `callIntrinsic_antitone_strike` — mul_le_mul_of_nonneg_right
    #[test]
    fn antitone_strike(s in 50.0f64..200.0, k1 in 50.0f64..100.0, extra in 0.0f64..50.0, d in 0.0f64..1.0) {
        prop_assert!(call_intrinsic(s, k1 + extra, d) <= call_intrinsic(s, k1, d) + 1e-10);
    }

    /// Lean: `call_spread_le_strike_diff` — 3-way case split
    #[test]
    fn spread_bounded(s in 50.0f64..200.0, k1 in 50.0f64..100.0, extra in 0.01f64..50.0, d in 0.0f64..1.0) {
        let k2 = k1 + extra;
        let spread = call_spread(s, k1, k2, d);
        prop_assert!(spread <= (k2 - k1) * d + 1e-10);
    }

    /// Lean: `intrinsic_parity` — le_or_gt + ring
    #[test]
    fn parity(s in 50.0f64..200.0, k in 50.0f64..200.0, d in 0.5f64..1.0) {
        let diff = call_intrinsic(s, k, d) - put_intrinsic(s, k, d);
        prop_assert!((diff - (s - k * d)).abs() < 1e-10);
    }
}
