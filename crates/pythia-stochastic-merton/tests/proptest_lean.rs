use proptest::prelude::*;
use pythia_stochastic_merton::*;

proptest! {
    /// compensated_drift is a trivial helper (returns lam*kappa by construction).
    /// Honest: this test only verifies the impl matches independent computation.
    /// NOT a meaningful safety property — it's an algebraic identity check.
    #[test]
    fn prop_compensated_drift_identity(
        mu in -100.0_f64..100.0,
        lam in -10.0_f64..10.0,
        kappa in -5.0_f64..5.0,
    ) {
        let result = compensated_drift(mu, lam, kappa);
        let expected = lam * kappa;
        prop_assert!((result - expected).abs() < 1e-12,
            "compensated_drift({mu}, {lam}, {kappa}) = {result}, expected {expected}");
    }

    /// Lean: total_variance proves result >= 0 when all inputs >= 0.
    #[test]
    fn prop_total_variance_nonneg(
        sigma_sq in 0.0_f64..100.0,
        delta_sq in 0.0_f64..100.0,
        kappa_sq in 0.0_f64..100.0,
        lam in 0.0_f64..100.0,
        t in 0.0_f64..100.0,
    ) {
        let tv = total_variance(sigma_sq, delta_sq, kappa_sq, lam, t);
        prop_assert!(tv >= 0.0,
            "total_variance({sigma_sq}, {delta_sq}, {kappa_sq}, {lam}, {t}) = {tv} < 0");
    }

    /// Lean: no_jump_probability proves exp(-lam*T) > 0.
    /// Range restricted to avoid f64 underflow (lam*t < 700).
    #[test]
    fn prop_no_jump_probability_positive(
        lam in 0.0_f64..20.0,
        t in 0.0_f64..20.0,
    ) {
        let p0 = no_jump_probability(lam, t);
        prop_assert!(p0 > 0.0,
            "no_jump_probability({lam}, {t}) = {p0} <= 0");
    }

    /// Lean: jump_adjusted_vol proves sigma_sq <= sigma_n_sq
    /// when T > 0, sigma_sq >= 0, delta_sq >= 0.
    #[test]
    fn prop_jump_adjusted_vol_geq_base(
        sigma_sq in 0.0_f64..100.0,
        delta_sq in 0.0_f64..100.0,
        n in 0_u64..1000,
        t in 0.001_f64..100.0,
    ) {
        let v = jump_adjusted_vol(sigma_sq, delta_sq, n, t);
        prop_assert!(v >= sigma_sq - 1e-12,
            "jump_adjusted_vol({sigma_sq}, {delta_sq}, {n}, {t}) = {v} < {sigma_sq}");
    }
}
