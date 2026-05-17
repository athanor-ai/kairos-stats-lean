//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (field_simp, log_exp, mul_nonneg, div_nonneg reasoning).

use proptest::prelude::*;
use pythia_risk_entropy::*;

proptest! {
    /// Lean: `entropic_risk_constant`
    /// rho_theta(c) = -c for any theta > 0 and any constant c.
    #[test]
    fn constant_property(theta in 0.01f64..10.0, c in -10.0f64..10.0) {
        prop_assert!(check_constant_property(theta, c, 1e-8));
    }

    /// Lean: `kl_penalty_nonneg`
    /// (1/theta)*kl >= 0 for theta > 0, kl >= 0.
    #[test]
    fn kl_penalty_nonneg(theta in 0.01f64..10.0, kl in 0.0f64..100.0) {
        prop_assert!(check_kl_penalty_nonneg(theta, kl));
    }

    /// Lean: `entropic_risk_finite`
    /// Entropic risk is well-defined (finite) for theta > 0, mgf > 0.
    #[test]
    fn risk_finite(theta in 0.01f64..10.0, mgf_val in 0.01f64..100.0) {
        let rho = entropic_risk(theta, mgf_val);
        prop_assert!(rho.is_finite());
    }

    /// Lean: `entropicRisk` monotonicity (derived from log monotonicity)
    /// Higher MGF gives higher entropic risk for theta > 0.
    #[test]
    fn monotone_in_mgf(theta in 0.01f64..10.0, m1 in 0.01f64..50.0, extra in 0.0f64..50.0) {
        let m2 = m1 + extra;
        prop_assert!(entropic_risk(theta, m1) <= entropic_risk(theta, m2) + 1e-12);
    }
}
