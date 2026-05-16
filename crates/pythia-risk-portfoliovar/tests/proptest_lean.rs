//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (PSD application, conv + ring, Finset.sum_comm).

use proptest::prelude::*;
use pythia_risk_portfoliovar::*;

fn psd_cov(v1: f64, v2: f64, rho: f64) -> Vec<Vec<f64>> {
    let c12 = rho * v1.sqrt() * v2.sqrt();
    vec![vec![v1, c12], vec![c12, v2]]
}

proptest! {
    /// Lean: `portfolioVar_nonneg` — PSD → nonneg
    #[test]
    fn var_nonneg(w1 in -2.0f64..2.0, w2 in -2.0f64..2.0, v1 in 0.01f64..0.1, v2 in 0.01f64..0.1, rho in -0.99f64..0.99) {
        let cov = psd_cov(v1, v2, rho);
        prop_assert!(portfolio_var(&[w1, w2], &cov) >= -1e-10);
    }

    /// Lean: `portfolioVar_scale` — Var(cw) = c²Var(w)
    #[test]
    fn var_scale(w1 in -1.0f64..1.0, w2 in -1.0f64..1.0, c in -5.0f64..5.0, v1 in 0.01f64..0.1, v2 in 0.01f64..0.1, rho in -0.99f64..0.99) {
        let cov = psd_cov(v1, v2, rho);
        let original = portfolio_var(&[w1, w2], &cov);
        let scaled = scaled_portfolio_var(c, &[w1, w2], &cov);
        prop_assert!((scaled - c * c * original).abs() < 1e-8);
    }

    /// Lean: `portfolioVar_single` — single asset = cov[k][k]
    #[test]
    fn single_asset(v1 in 0.01f64..0.1, v2 in 0.01f64..0.1, rho in -0.99f64..0.99) {
        let cov = psd_cov(v1, v2, rho);
        let var0 = portfolio_var(&[1.0, 0.0], &cov);
        prop_assert!((var0 - cov[0][0]).abs() < 1e-10);
    }

    /// Lean: `portfolioVar_zero_weights`
    #[test]
    fn zero_weights(v1 in 0.01f64..0.1, v2 in 0.01f64..0.1) {
        let cov = psd_cov(v1, v2, 0.0);
        prop_assert_eq!(portfolio_var(&[0.0, 0.0], &cov), 0.0);
    }
}
