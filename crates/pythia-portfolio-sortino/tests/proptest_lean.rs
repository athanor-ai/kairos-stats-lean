//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_sortino::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `sortinoRatio_scale_invariant`
    /// For any alpha > 0, sortino(alpha*mu, alpha*rf, alpha*sigma_d) == sortino(mu, rf, sigma_d).
    #[test]
    fn prop_scale_invariance(
        mu in -1000.0..1000.0f64,
        rf in -1000.0..1000.0f64,
        sigma_d in 0.001..1000.0f64,
        alpha in 0.001..1000.0f64,
    ) {
        let base = sortino_ratio(mu, rf, sigma_d);
        let scaled = sortino_ratio_scaled(alpha, mu, rf, sigma_d);
        prop_assert!((base - scaled).abs() < EPS * (1.0 + base.abs()),
            "scale invariance violated: base={}, scaled={}", base, scaled);
    }

    /// Lean: `sortinoRatio_mono_excess`
    /// For fixed sigma_d > 0, if excess1 <= excess2 then sortino1 <= sortino2.
    #[test]
    fn prop_monotone_excess(
        excess1 in -1000.0..1000.0f64,
        delta in 0.0..1000.0f64,
        sigma_d in 0.001..1000.0f64,
    ) {
        let excess2 = excess1 + delta;
        let s1 = sortino_ratio(excess1, 0.0, sigma_d);
        let s2 = sortino_ratio(excess2, 0.0, sigma_d);
        prop_assert!(s1 <= s2 + EPS,
            "monotonicity violated: s1={}, s2={}, excess1={}, excess2={}", s1, s2, excess1, excess2);
    }

    /// Lean: `sortinoRatio_pos`
    /// Positive excess and positive sigma_d => positive ratio.
    #[test]
    fn prop_pos_when_excess_pos(
        excess in 0.001..1000.0f64,
        sigma_d in 0.001..1000.0f64,
    ) {
        let mu = excess; // rf = 0
        let r = sortino_ratio(mu, 0.0, sigma_d);
        prop_assert!(r > 0.0, "expected positive ratio for positive excess, got {}", r);
        prop_assert!(sortino_ratio_is_positive(mu, 0.0, sigma_d));
    }
}
