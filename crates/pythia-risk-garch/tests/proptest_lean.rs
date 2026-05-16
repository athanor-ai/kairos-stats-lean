//! Provenance: VERIFIED — the Lean proofs in `Pythia.Finance.Risk.GARCHUpdate` use
//! `mul_nonneg`, `sq_nonneg`, `linarith`, `div_pos`, and `field_simp` + `ring`
//! to establish all results non-tautologically. These proptests exercise the same
//! invariants in Rust.

use proptest::prelude::*;
use pythia_risk_garch::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `garchUpdate_nonneg`
    /// If omega, alpha, beta, sigma_sq >= 0, then garch_update >= 0.
    #[test]
    fn prop_update_nonneg(
        omega in 0.0..1.0f64,
        alpha in 0.0..0.5f64,
        beta in 0.0..0.5f64,
        eps in -10.0..10.0f64,
        sigma_sq in 0.0..1.0f64,
    ) {
        let result = garch_update(omega, alpha, beta, eps, sigma_sq);
        prop_assert!(result >= 0.0,
            "non-negativity violated: result={}, omega={}, alpha={}, beta={}, eps={}, sigma_sq={}",
            result, omega, alpha, beta, eps, sigma_sq);
    }

    /// Lean: `garchStationaryVariance_pos`
    /// Under omega > 0 and alpha + beta < 1, stationary variance is positive.
    #[test]
    fn prop_stationary_variance_pos(
        omega in 0.001..1.0f64,
        alpha in 0.0..0.4f64,
        beta in 0.0..0.5f64,
    ) {
        prop_assume!(alpha + beta < 1.0);
        let sv = garch_stationary_variance(omega, alpha, beta);
        prop_assert!(sv > 0.0,
            "stationary variance not positive: sv={}, omega={}, alpha={}, beta={}",
            sv, omega, alpha, beta);
    }

    /// Lean: `garchStationaryVariance_recurrence`
    /// sigma_sq_inf = omega + (alpha + beta) * sigma_sq_inf.
    #[test]
    fn prop_recurrence(
        omega in 0.001..1.0f64,
        alpha in 0.0..0.4f64,
        beta in 0.0..0.5f64,
    ) {
        prop_assume!(alpha + beta < 1.0);
        let err = garch_recurrence_error(omega, alpha, beta);
        prop_assert!(err < EPS,
            "recurrence violated: error={}, omega={}, alpha={}, beta={}",
            err, omega, alpha, beta);
    }

    /// Structural: update is monotone in sigma_sq (for beta > 0).
    #[test]
    fn prop_monotone_in_sigma_sq(
        omega in 0.0..0.1f64,
        alpha in 0.0..0.3f64,
        beta in 0.01..0.5f64,
        eps in -5.0..5.0f64,
        sigma_sq1 in 0.0..1.0f64,
        delta in 0.0..1.0f64,
    ) {
        let sigma_sq2 = sigma_sq1 + delta;
        let u1 = garch_update(omega, alpha, beta, eps, sigma_sq1);
        let u2 = garch_update(omega, alpha, beta, eps, sigma_sq2);
        prop_assert!(u1 <= u2 + EPS,
            "monotonicity violated: u1={}, u2={}", u1, u2);
    }
}
