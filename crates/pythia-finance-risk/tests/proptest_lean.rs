use proptest::prelude::*;
use pythia_finance_risk::*;

proptest! {
    /// Lean: `subadditivity` + `diversification_benefit`
    #[test]
    fn subadditive_implies_nonneg_benefit(rho_x in 0.0f64..100.0, rho_y in 0.0f64..100.0, reduction in 0.0f64..50.0) {
        let rho_xy = rho_x + rho_y - reduction;
        if check_subadditivity(rho_xy, rho_x, rho_y) {
            prop_assert!(diversification_benefit(rho_xy, rho_x, rho_y) >= -1e-10);
        }
    }

    /// Lean: `translation_invariance`
    #[test]
    fn translation_invariance(rho_x in -100.0f64..100.0, c in -50.0f64..50.0) {
        let rho_xc = rho_x - c;
        prop_assert!(check_translation_invariance(rho_x, rho_xc, c, 1e-10));
    }

    /// Lean: `positive_homogeneity`
    #[test]
    fn positive_homogeneity(rho_x in -100.0f64..100.0, lambda in 0.01f64..10.0) {
        let rho_lx = lambda * rho_x;
        prop_assert!(check_positive_homogeneity(rho_x, rho_lx, lambda, 1e-10));
    }

    /// Lean: `risk_capital_makes_acceptable`
    #[test]
    fn capital_zeroes_risk(rho in 0.0f64..1e8) {
        let capital = required_capital(rho);
        prop_assert!((capital - rho).abs() < 1e-10);
    }
}
