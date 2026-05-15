use proptest::prelude::*;
use pythia_stochastic_regime::RegimeModel;

proptest! {
    /// Lean: `stationary_dist_sum`
    #[test]
    fn stationary_sums_to_one(p12 in 0.01f64..0.99, p21 in 0.01f64..0.99) {
        let m = RegimeModel::new(p12, p21);
        prop_assert!((m.pi1() + m.pi2() - 1.0).abs() < 1e-10);
    }

    /// Lean: `stationary_dist_pos`
    #[test]
    fn stationary_pos(p12 in 0.01f64..0.99, p21 in 0.01f64..0.99) {
        let m = RegimeModel::new(p12, p21);
        prop_assert!(m.pi1() > 0.0);
        prop_assert!(m.pi2() > 0.0);
    }

    /// Lean: `expected_duration_pos`
    #[test]
    fn duration_pos(p12 in 0.01f64..0.99, p21 in 0.01f64..0.99) {
        let m = RegimeModel::new(p12, p21);
        prop_assert!(m.duration1() > 0.0);
        prop_assert!(m.duration2() > 0.0);
    }

    /// Lean: `regime_weighted_var_nonneg`
    #[test]
    fn weighted_var_nonneg(p12 in 0.01f64..0.99, p21 in 0.01f64..0.99, v1 in 0.0f64..0.1, v2 in 0.0f64..0.1) {
        let m = RegimeModel::new(p12, p21);
        prop_assert!(m.weighted_variance(v1, v2) >= -1e-15);
    }
}
