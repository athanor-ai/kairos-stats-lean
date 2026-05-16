//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_calmar::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `calmarRatio_pos`
    /// For R > 0 and MDD_abs > 0, the Calmar ratio is strictly positive.
    #[test]
    fn prop_positivity(
        r in 0.001..1e6_f64,
        mdd_abs in 0.001..1e6_f64,
    ) {
        let cr = calmar_ratio(r, mdd_abs);
        prop_assert!(cr > 0.0, "expected positive Calmar for R={}, MDD={}, got {}", r, mdd_abs, cr);
        prop_assert!(calmar_ratio_is_positive(r, mdd_abs));
    }

    /// Lean: `calmarRatio_mono_return`
    /// For fixed MDD_abs > 0, if R1 <= R2 then calmar(R1) <= calmar(R2).
    #[test]
    fn prop_monotone_return(
        r1 in -1e3..1e3_f64,
        delta in 0.0..1e3_f64,
        mdd_abs in 0.001..1e3_f64,
    ) {
        let r2 = r1 + delta;
        let cr1 = calmar_ratio(r1, mdd_abs);
        let cr2 = calmar_ratio(r2, mdd_abs);
        prop_assert!(cr1 <= cr2 + EPS,
            "monotonicity violated: cr1={}, cr2={}, R1={}, R2={}", cr1, cr2, r1, r2);
    }

    /// Lean: `calmarRatio_antitone_mdd`
    /// For R >= 0, 0 < M1 <= M2, calmar(R, M2) <= calmar(R, M1).
    #[test]
    fn prop_antitone_mdd(
        r in 0.0..1e6_f64,
        m1 in 0.001..1e3_f64,
        delta in 0.0..1e3_f64,
    ) {
        let m2 = m1 + delta;
        let cr1 = calmar_ratio(r, m1);
        let cr2 = calmar_ratio(r, m2);
        prop_assert!(cr2 <= cr1 + EPS,
            "antitonicity violated: calmar(m1={})={}, calmar(m2={})={}", m1, cr1, m2, cr2);
    }
}
