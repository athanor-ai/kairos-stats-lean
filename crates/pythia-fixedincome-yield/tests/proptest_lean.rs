use proptest::prelude::*;
use pythia_fixedincome_yield::*;

proptest! {
    /// Lean: `discrete_forward_nonneg` — forward rate nonneg when D1 ≥ D2
    #[test]
    fn forward_nonneg(d1 in 0.5f64..1.0, decrease in 0.0f64..0.3, dt in 0.1f64..10.0) {
        let d2 = d1 - decrease;
        if d2 > 0.0 {
            prop_assert!(forward_rate(d1, d2, dt) >= -1e-12);
        }
    }

    /// Lean: `convexity_benefit` — C/2 * dy² ≥ 0
    #[test]
    fn convexity_benefit_nonneg(c in 0.0f64..200.0, dy in -0.1f64..0.1) {
        prop_assert!(convexity_benefit(c, dy) >= -1e-15);
    }

    /// Lean: `discount_factor_bounded` — valid curve passes validation
    #[test]
    fn monotone_curve_valid(d0 in 0.9f64..1.0, drop1 in 0.01f64..0.1, drop2 in 0.01f64..0.1) {
        let d1 = d0 - drop1;
        let d2 = d1 - drop2;
        if d2 > 0.0 {
            let curve = vec![
                DiscountPoint { maturity: 0.0, discount: d0 },
                DiscountPoint { maturity: 1.0, discount: d1 },
                DiscountPoint { maturity: 2.0, discount: d2 },
            ];
            prop_assert_eq!(validate_curve(&curve), CurveValidity::Valid);
        }
    }

    /// Lean: `key_rate_sum`
    #[test]
    fn krd_sum(k1 in 0.0f64..5.0, k2 in 0.0f64..5.0, k3 in 0.0f64..5.0) {
        let total = k1 + k2 + k3;
        prop_assert!(check_key_rate_sum(&[k1, k2, k3], total, 1e-10));
    }
}
