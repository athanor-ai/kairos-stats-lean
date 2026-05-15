use proptest::prelude::*;
use pythia_hft_fixedpoint_strong::TrackedFP;

const SCALE: u32 = 65536;

proptest! {
    /// Lean: `add_error_bound` — addition error ≤ sum of input errors
    #[test]
    fn add_error_tracked(a_real in -1000.0f64..1000.0, b_real in -1000.0f64..1000.0) {
        let a = TrackedFP::from_real(a_real, SCALE);
        let b = TrackedFP::from_real(b_real, SCALE);
        let sum = a.add(b);
        let actual_error = ((a_real + b_real) - sum.to_real()).abs();
        prop_assert!(actual_error <= sum.error_bound + 1e-10,
            "actual {actual_error} > bound {}", sum.error_bound);
    }

    /// Lean: `mul_error_first_order` — multiplication error tracked
    #[test]
    fn mul_error_tracked(a_real in -100.0f64..100.0, b_real in -100.0f64..100.0) {
        let a = TrackedFP::from_real(a_real, SCALE);
        let b = TrackedFP::from_real(b_real, SCALE);
        let product = a.mul(b);
        let actual_error = ((a_real * b_real) - product.to_real()).abs();
        prop_assert!(actual_error <= product.error_bound + 1e-6,
            "actual {actual_error} > bound {}", product.error_bound);
    }

    /// Lean: `compare_preserves_order` — far-apart values always ordered correctly
    #[test]
    fn compare_far_values(a_real in -1000.0f64..0.0, b_real in 1.0f64..1000.0) {
        let a = TrackedFP::from_real(a_real, SCALE);
        let b = TrackedFP::from_real(b_real, SCALE);
        if let Some(ord) = a.safe_cmp(&b) {
            prop_assert_eq!(ord, std::cmp::Ordering::Less);
        }
    }

    /// Lean: `n_step_add_error` — chain error is linear
    #[test]
    fn chain_error_linear(n in 1usize..1000) {
        let eps = 0.5 / SCALE as f64;
        let bound = TrackedFP::chain_error_bound(n, eps);
        prop_assert!((bound - n as f64 * eps).abs() < 1e-15);
    }

    /// Lean: `no_overflow_from_abs_bound` — small values don't overflow
    #[test]
    fn small_values_no_overflow(a in -1_000_000i64..1_000_000, b in -1_000_000i64..1_000_000) {
        let fa = TrackedFP::exact(a, SCALE);
        let fb = TrackedFP::exact(b, SCALE);
        prop_assert!(!fa.would_overflow(&fb, i64::MAX));
    }
}
