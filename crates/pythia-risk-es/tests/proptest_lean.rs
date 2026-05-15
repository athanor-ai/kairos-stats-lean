use proptest::prelude::*;
use pythia_risk_es::*;

proptest! {
    /// Lean: `esNormal_dominates_varNormal` — ES ≥ VaR when h ≥ z, σ ≥ 0
    #[test]
    fn es_dominates_var(mu in -1.0f64..1.0, sigma in 0.0f64..1.0, z in 1.0f64..3.0, extra in 0.0f64..2.0) {
        let h = z + extra;
        prop_assert!(es_normal(mu, sigma, h) >= var_normal(mu, sigma, z) - 1e-10);
    }

    /// Lean: `esNormal_pos_homogeneous`
    #[test]
    fn pos_homogeneous(alpha in 0.0f64..10.0, mu in -1.0f64..1.0, sigma in 0.0f64..1.0, h in 1.0f64..3.0) {
        prop_assert!(check_pos_homogeneous(alpha, mu, sigma, h, 1e-8));
    }

    /// Lean: `esNormal_translation`
    #[test]
    fn translation(mu in -1.0f64..1.0, sigma in 0.0f64..1.0, h in 1.0f64..3.0, c in -1.0f64..1.0) {
        prop_assert!(check_translation(mu, sigma, h, c, 1e-10));
    }

    /// Lean: `esNormal_zero_mean`
    #[test]
    fn zero_mean(sigma in 0.0f64..1.0, h in 1.0f64..3.0) {
        prop_assert!((es_normal(0.0, sigma, h) - sigma * h).abs() < 1e-10);
    }
}
