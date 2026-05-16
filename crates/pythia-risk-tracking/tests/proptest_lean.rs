//! Provenance: VERIFIED — the Lean proofs in `Pythia.Finance.Risk.TrackingError`
//! use `le_max_right`, `sqrt_nonneg`, `sq_sqrt`, and `simp` to establish these
//! properties non-tautologically. These proptests exercise the same invariants in Rust.

use proptest::prelude::*;
use pythia_risk_tracking::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `trackingVariance_nonneg`
    /// For any real V, tracking_variance(V) >= 0.
    #[test]
    fn prop_variance_nonneg(v in -1000.0f64..1000.0) {
        prop_assert!(tracking_variance(v) >= 0.0,
            "variance nonneg violated for v={}", v);
    }

    /// Lean: `trackingError_nonneg`
    /// For any real V, tracking_error(V) >= 0.
    #[test]
    fn prop_error_nonneg(v in -1000.0f64..1000.0) {
        prop_assert!(tracking_error(v) >= 0.0,
            "error nonneg violated for v={}", v);
    }

    /// Lean: `trackingError_sq`
    /// tracking_error(V)^2 = tracking_variance(V).
    #[test]
    fn prop_square_link(v in -1000.0f64..1000.0) {
        let tv = tracking_variance(v);
        let te_sq = tracking_error_squared(v);
        prop_assert!((te_sq - tv).abs() < EPS * (1.0 + tv),
            "square link violated: te_sq={}, tv={}", te_sq, tv);
    }

    /// Lean: `trackingVariance_zero_active_return` (generalised)
    /// Empirical variance of a constant series is zero.
    #[test]
    fn prop_constant_series_zero(c in -100.0f64..100.0, n in 2usize..20) {
        let series: Vec<f64> = vec![c; n];
        let tv = empirical_tracking_variance(&series);
        prop_assert!(tv < EPS,
            "constant series should have zero variance, got {}", tv);
    }
}
