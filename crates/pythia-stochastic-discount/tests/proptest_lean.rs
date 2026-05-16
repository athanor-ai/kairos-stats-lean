//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_stochastic_discount::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `sdfPrice_at_zero_cov`
    /// At zero covariance, price = m_mean * payoff_mean.
    #[test]
    fn prop_zero_cov(
        m_mean in -1e3..1e3_f64,
        payoff_mean in -1e3..1e3_f64,
    ) {
        let p = sdf_price(m_mean, 0.0, payoff_mean);
        let expected = m_mean * payoff_mean;
        prop_assert!((p - expected).abs() < EPS * (1.0 + expected.abs()),
            "zero-cov price mismatch: p={}, expected={}", p, expected);
    }

    /// Lean: `hansenJagannathanBound_nonneg`
    /// For return_vol > 0, the HJ bound is non-negative.
    #[test]
    fn prop_hj_bound_nonneg(
        excess_return in -1e3..1e3_f64,
        return_vol in 0.001..1e3_f64,
    ) {
        let b = hansen_jagannathan_bound(excess_return, return_vol);
        prop_assert!(b >= 0.0,
            "HJ bound negative: b={}, er={}, vol={}", b, excess_return, return_vol);
    }

    /// Lean: `hansenJagannathanBound_zero_excess`
    /// At zero excess return, bound = 0.
    #[test]
    fn prop_hj_bound_zero_excess(
        return_vol in 0.001..1e3_f64,
    ) {
        let b = hansen_jagannathan_bound(0.0, return_vol);
        prop_assert!(b.abs() < EPS,
            "HJ bound not zero at zero excess: b={}", b);
    }

    /// Lean: `hansenJagannathanBound_mono_excess`
    /// For |er1| <= |er2|, bound(er1) <= bound(er2).
    #[test]
    fn prop_hj_bound_mono(
        er1 in 0.0..1e3_f64,
        delta in 0.0..1e3_f64,
        return_vol in 0.001..1e3_f64,
    ) {
        let er2 = er1 + delta;
        let b1 = hansen_jagannathan_bound(er1, return_vol);
        let b2 = hansen_jagannathan_bound(er2, return_vol);
        prop_assert!(b1 <= b2 + EPS,
            "monotonicity violated: b1={}, b2={}, er1={}, er2={}", b1, b2, er1, er2);
    }
}
