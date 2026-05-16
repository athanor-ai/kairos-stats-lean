use proptest::prelude::*;
use pythia_portfolio_capm::*;

proptest! {
    /// Lean: capm_expected_return: ERi - Rf = beta * (ERm - Rf)
    #[test]
    fn prop_capm_excess_return(
        rf in -1.0_f64..1.0,
        beta in -5.0_f64..5.0,
        erm in -1.0_f64..1.0,
    ) {
        let eri = capm_expected_return(rf, beta, erm);
        let excess = eri - rf;
        let expected = beta * (erm - rf);
        prop_assert!((excess - expected).abs() < 1e-10,
            "capm_excess failed: excess={excess}, expected={expected}");
    }

    /// Lean: zero_beta_return: beta=0 => E[R_i] = R_f
    #[test]
    fn prop_zero_beta(
        rf in -1.0_f64..1.0,
        erm in -1.0_f64..1.0,
    ) {
        let eri = capm_expected_return(rf, 0.0, erm);
        prop_assert!((eri - rf).abs() < 1e-12,
            "zero_beta failed: eri={eri}, rf={rf}");
    }

    /// Lean: market_beta: Rf + 1*(ERm - Rf) = ERm
    #[test]
    fn prop_market_beta(
        rf in -1.0_f64..1.0,
        erm in -1.0_f64..1.0,
    ) {
        let eri = capm_expected_return(rf, 1.0, erm);
        prop_assert!((eri - erm).abs() < 1e-12,
            "market_beta failed: eri={eri}, erm={erm}");
    }

    /// Lean: r_squared_bound: R^2 = beta_sq*var_m/var_i <= 1
    /// when var_eps >= 0, var_i > 0, var_i = beta_sq*var_m + var_eps
    #[test]
    fn prop_r_squared_bound(
        beta in -3.0_f64..3.0,
        var_m in 0.001_f64..1.0,
        var_eps in 0.0_f64..1.0,
    ) {
        let beta_sq = beta * beta;
        let var_i = beta_sq * var_m + var_eps;
        if var_i > 0.0 {
            let rsq = r_squared(beta_sq, var_m, var_i);
            prop_assert!(rsq <= 1.0 + 1e-12,
                "r_squared_bound failed: rsq={rsq}");
            prop_assert!(rsq >= -1e-12,
                "r_squared negative: rsq={rsq}");
        }
    }
}
