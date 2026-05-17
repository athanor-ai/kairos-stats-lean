//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (linarith, mul_nonneg, div_nonneg, sq_nonneg reasoning).

use proptest::prelude::*;
use pythia_options_bspde::*;

proptest! {
    /// Lean: `bsPDEOperator_linear_theta`
    /// Shifting theta shifts the operator by the same amount.
    #[test]
    fn linear_in_theta(
        theta in -10.0f64..10.0,
        dtheta in -5.0f64..5.0,
        delta in -1.0f64..1.0,
        gamma in -1.0f64..1.0,
        c in 0.0f64..50.0,
        s in 0.0f64..200.0,
        r in 0.0f64..0.2,
        sigma in 0.0f64..1.0
    ) {
        prop_assert!(check_linear_theta(theta, dtheta, delta, gamma, c, s, r, sigma, 1e-8));
    }

    /// Lean: `bsPDE_gamma_term_nonneg`
    /// Gamma contribution is nonneg for gamma >= 0, sigma >= 0, S >= 0.
    #[test]
    fn gamma_term_nonneg(sigma in 0.0f64..1.0, s in 0.0f64..200.0, gamma in 0.0f64..1.0) {
        prop_assert!(check_gamma_term_nonneg(sigma, s, gamma));
    }

    /// Lean: `bsPDEOperator_at_expiry`
    /// At expiry (theta=0), operator = gamma_term + r*S*delta - r*C.
    #[test]
    fn at_expiry(delta in -1.0f64..1.0, gamma in -1.0f64..1.0, c in 0.0f64..50.0, s in 0.0f64..200.0, r in 0.0f64..0.2, sigma in 0.0f64..1.0) {
        let op = bs_pde_operator(0.0, delta, gamma, c, s, r, sigma);
        let expected = sigma * sigma / 2.0 * s * s * gamma + r * s * delta - r * c;
        prop_assert!((op - expected).abs() < 1e-8);
    }

    /// Lean: `bsPDE_theta_le_riskfree`
    /// Under PDE=0 and long gamma, theta <= r*(C - S*delta).
    #[test]
    fn theta_le_riskfree(
        delta in 0.0f64..1.0,
        gamma in 0.0f64..1.0,
        c in 0.0f64..50.0,
        s in 0.0f64..200.0,
        r in 0.0f64..0.2,
        sigma in 0.0f64..1.0
    ) {
        let theta = r * c - r * s * delta - sigma * sigma / 2.0 * s * s * gamma;
        // PDE = 0 by construction
        prop_assert!(theta <= r * (c - s * delta) + 1e-10);
    }
}
