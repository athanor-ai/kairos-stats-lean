//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_risk_var::*;

proptest! {
    /// Lean: `varNormal_pos_homogeneous`
    #[test]
    fn pos_homogeneous(alpha in 0.0f64..10.0, mu in -1.0f64..1.0, sigma in 0.0f64..1.0, z in 0.0f64..3.0) {
        prop_assert!(check_pos_homogeneous(alpha, mu, sigma, z, 1e-8));
    }

    /// Lean: `varNormal_translation`
    #[test]
    fn translation(mu in -1.0f64..1.0, sigma in 0.0f64..1.0, z in 0.0f64..3.0, c in -1.0f64..1.0) {
        prop_assert!(check_translation(mu, sigma, z, c, 1e-10));
    }

    /// Lean: `varNormal_mono_in_sigma` — higher σ → higher VaR for z ≥ 0
    #[test]
    fn mono_sigma(mu in -1.0f64..1.0, s1 in 0.0f64..0.5, extra in 0.0f64..0.5, z in 0.0f64..3.0) {
        prop_assert!(var_normal(mu, s1, z) <= var_normal(mu, s1 + extra, z) + 1e-12);
    }

    /// Lean: `varNormal_zero_mean`
    #[test]
    fn zero_mean(sigma in 0.0f64..1.0, z in 0.0f64..3.0) {
        prop_assert!((var_normal(0.0, sigma, z) - sigma * z).abs() < 1e-10);
    }
}
