//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_risk_vol_smile::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `impliedVol_atm`
    /// At m = 0, implied vol always equals sigma_atm.
    #[test]
    fn prop_atm_level(
        sigma_atm in -100.0..100.0_f64,
        skew in -10.0..10.0_f64,
        smile in -10.0..10.0_f64,
    ) {
        let v = implied_vol(sigma_atm, skew, smile, 0.0);
        prop_assert!((v - sigma_atm).abs() < EPS,
            "ATM level violated: v={}, sigma_atm={}", v, sigma_atm);
    }

    /// Lean: `impliedVol_symmetric_no_skew`
    /// With skew=0, vol(m) = vol(-m).
    #[test]
    fn prop_symmetry_no_skew(
        sigma_atm in -100.0..100.0_f64,
        smile in -10.0..10.0_f64,
        m in -100.0..100.0_f64,
    ) {
        let v_pos = implied_vol(sigma_atm, 0.0, smile, m);
        let v_neg = implied_vol(sigma_atm, 0.0, smile, -m);
        prop_assert!((v_pos - v_neg).abs() < EPS * (1.0 + v_pos.abs()),
            "symmetry violated: v(m)={}, v(-m)={}", v_pos, v_neg);
    }

    /// Lean: `impliedVol_mono_smile`
    /// For smile1 <= smile2, implied_vol(..., smile1, m) <= implied_vol(..., smile2, m).
    #[test]
    fn prop_mono_smile(
        sigma_atm in -100.0..100.0_f64,
        skew in -10.0..10.0_f64,
        smile1 in -10.0..10.0_f64,
        delta in 0.0..10.0_f64,
        m in -100.0..100.0_f64,
    ) {
        let smile2 = smile1 + delta;
        let v1 = implied_vol(sigma_atm, skew, smile1, m);
        let v2 = implied_vol(sigma_atm, skew, smile2, m);
        // m^2 >= 0, so delta * m^2 >= 0 => v2 >= v1
        prop_assert!(v1 <= v2 + EPS,
            "monotonicity in smile violated: v1={}, v2={}, smile1={}, smile2={}, m={}",
            v1, v2, smile1, smile2, m);
    }

    /// Lean: `impliedVol_quadratic_form`
    /// Definition identity: vol = sigma_atm + skew*m + smile*m^2.
    #[test]
    fn prop_quadratic_form(
        sigma_atm in -100.0..100.0_f64,
        skew in -10.0..10.0_f64,
        smile in -10.0..10.0_f64,
        m in -100.0..100.0_f64,
    ) {
        let v = implied_vol(sigma_atm, skew, smile, m);
        let expected = sigma_atm + skew * m + smile * m * m;
        prop_assert!((v - expected).abs() < EPS * (1.0 + expected.abs()),
            "quadratic form mismatch: v={}, expected={}", v, expected);
    }
}
