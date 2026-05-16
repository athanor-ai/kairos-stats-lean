//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_fixedincome_perpetuity::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `perpetuityValue_pos`
    /// For C > 0 and r > 0, PV is strictly positive.
    #[test]
    fn prop_positivity(
        c in 0.001..1e6_f64,
        r in 0.001..1e3_f64,
    ) {
        let pv = perpetuity_value(c, r);
        prop_assert!(pv > 0.0, "expected positive PV for C={}, r={}, got {}", c, r, pv);
        prop_assert!(perpetuity_value_is_positive(c, r));
    }

    /// Lean: `perpetuityValue_nonneg`
    /// For C >= 0 and r > 0, PV is non-negative.
    #[test]
    fn prop_nonneg(
        c in 0.0..1e6_f64,
        r in 0.001..1e3_f64,
    ) {
        let pv = perpetuity_value(c, r);
        prop_assert!(pv >= 0.0, "expected non-negative PV for C={}, r={}, got {}", c, r, pv);
    }

    /// Lean: `perpetuityValue_antitone_rate`
    /// For C >= 0, 0 < r1 <= r2, PV(C, r2) <= PV(C, r1).
    #[test]
    fn prop_antitone_rate(
        c in 0.0..1e6_f64,
        r1 in 0.001..1e3_f64,
        delta in 0.0..1e3_f64,
    ) {
        let r2 = r1 + delta;
        let pv1 = perpetuity_value(c, r1);
        let pv2 = perpetuity_value(c, r2);
        prop_assert!(pv2 <= pv1 + EPS,
            "antitonicity violated: PV(r1={})={}, PV(r2={})={}", r1, pv1, r2, pv2);
    }

    /// Lean: definition identity PV = C / r
    #[test]
    fn prop_definition_identity(
        c in -1e6..1e6_f64,
        r in 0.001..1e3_f64,
    ) {
        let pv = perpetuity_value(c, r);
        let expected = c / r;
        prop_assert!((pv - expected).abs() < EPS * (1.0 + expected.abs()),
            "definition mismatch: pv={}, c/r={}", pv, expected);
    }
}
