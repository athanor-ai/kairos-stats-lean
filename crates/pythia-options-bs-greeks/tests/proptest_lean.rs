//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (unfold + div_nonneg, positivity, mul_nonneg chains).

use proptest::prelude::*;
use pythia_options_bs_greeks::*;

proptest! {
    /// Lean: `bsDelta_bounded` — unfold bsDelta; exact (hPhi_nonneg, hPhi_le_one)
    #[test]
    fn delta_bounded(
        s in 50.0f64..200.0,
        k in 50.0f64..200.0,
        t in 0.01f64..5.0,
        r in -0.05f64..0.2,
        sigma in 0.05f64..1.0
    ) {
        let d = bs_delta(s, k, t, r, sigma);
        prop_assert!(d >= -1e-10, "delta={} < 0", d);
        prop_assert!(d <= 1.0 + 1e-10, "delta={} > 1", d);
    }

    /// Lean: `bsGamma_nonneg` — div_nonneg + positivity (S,sigma,T > 0)
    #[test]
    fn gamma_nonneg(
        s in 10.0f64..200.0,
        k in 10.0f64..200.0,
        t in 0.01f64..5.0,
        r in -0.05f64..0.2,
        sigma in 0.05f64..1.0
    ) {
        let g = bs_gamma(s, k, t, r, sigma);
        prop_assert!(g >= -1e-10, "gamma={} < 0", g);
    }

    /// Lean: `bsVega_nonneg` — mul_nonneg (mul_nonneg hS (hphi_nonneg _)) hsqrtT
    #[test]
    fn vega_nonneg(
        s in 0.01f64..200.0,
        k in 10.0f64..200.0,
        t in 0.01f64..5.0,
        r in -0.05f64..0.2,
        sigma in 0.05f64..1.0
    ) {
        let v = bs_vega(s, k, t, r, sigma);
        prop_assert!(v >= -1e-10, "vega={} < 0", v);
    }

    /// Lean: `bsRho_nonneg` — mul_nonneg chain (K,T >= 0, exp >= 0, Phi >= 0)
    #[test]
    fn rho_nonneg(
        s in 10.0f64..200.0,
        k in 0.01f64..200.0,
        t in 0.01f64..5.0,
        r in -0.05f64..0.2,
        sigma in 0.05f64..1.0
    ) {
        let rho = bs_rho(s, k, t, r, sigma);
        prop_assert!(rho >= -1e-10, "rho={} < 0", rho);
    }
}
