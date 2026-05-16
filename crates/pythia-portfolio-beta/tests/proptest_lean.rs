//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content.

use proptest::prelude::*;
use pythia_portfolio_beta::*;

proptest! {
    /// Lean: `betaFromCorrelation_zero_corr` — zero correlation implies zero beta
    #[test]
    fn zero_corr_zero_beta(sigma_p in 0.01f64..1.0, sigma_m in 0.01f64..1.0) {
        prop_assert!((beta_from_correlation(0.0, sigma_p, sigma_m)).abs() < 1e-15);
    }

    /// Lean: `betaFromCorrelation_unit_corr` — unit correlation gives vol ratio
    #[test]
    fn unit_corr_vol_ratio(sigma_p in 0.01f64..1.0, sigma_m in 0.01f64..1.0) {
        let beta = beta_from_correlation(1.0, sigma_p, sigma_m);
        let expected = sigma_p / sigma_m;
        prop_assert!((beta - expected).abs() < 1e-12);
    }

    /// Lean: `betaFromCorrelation_scale_p` — scaling sigma_p by alpha scales beta by alpha
    #[test]
    fn scale_p(rho in -1.0f64..1.0, sigma_p in 0.01f64..1.0, sigma_m in 0.01f64..1.0, alpha in 0.1f64..5.0) {
        let beta_base = beta_from_correlation(rho, sigma_p, sigma_m);
        let beta_scaled = beta_from_correlation(rho, alpha * sigma_p, sigma_m);
        prop_assert!((beta_scaled - alpha * beta_base).abs() < 1e-10);
    }
}
