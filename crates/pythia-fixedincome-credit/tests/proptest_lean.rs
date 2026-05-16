//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_fixedincome_credit::*;

proptest! {
    /// `cum_pd_mono`: cumulative PD is monotone in time for nonneg hazard rate.
    #[test]
    fn prop_cum_pd_mono(
        h in 0.0001f64..1.0,
        t1 in 0.01f64..30.0,
        delta in 0.0f64..30.0,
    ) {
        let t2 = t1 + delta;
        let pd1 = cumulative_pd(h, t1);
        let pd2 = cumulative_pd(h, t2);
        prop_assert!(pd1 <= pd2 + 1e-12,
            "cum_pd_mono violated: PD({}) = {} > PD({}) = {}", t1, pd1, t2, pd2);
    }

    /// `survival_antitone`: survival probability is antitone in time.
    #[test]
    fn prop_survival_antitone(
        h in 0.0001f64..1.0,
        t1 in 0.01f64..30.0,
        delta in 0.0f64..30.0,
    ) {
        let t2 = t1 + delta;
        let s1 = survival_probability(h, t1);
        let s2 = survival_probability(h, t2);
        prop_assert!(s2 <= s1 + 1e-12,
            "survival_antitone violated: S({}) = {} > S({}) = {}", t2, s2, t1, s1);
    }

    /// `risky_discount_le_riskfree`: risky discount <= riskfree discount
    /// when survival in [0, 1].
    #[test]
    fn prop_risky_discount_le_riskfree(
        d_rf in 0.0f64..1.0,
        s in 0.0f64..1.0,
    ) {
        let d_risky = risky_discount(d_rf, s);
        prop_assert!(d_risky <= d_rf + 1e-12,
            "risky_discount_le_riskfree violated: {} > {}", d_risky, d_rf);
    }

    /// `spread_mono_hazard`: spread is monotone in hazard rate for fixed recovery < 1.
    #[test]
    fn prop_spread_mono_hazard(
        h1 in 0.0f64..0.5,
        delta in 0.0f64..0.5,
        r in 0.0f64..0.99,
    ) {
        let h2 = h1 + delta;
        let s1 = credit_spread(h1, r);
        let s2 = credit_spread(h2, r);
        prop_assert!(s1 <= s2 + 1e-12,
            "spread_mono_hazard violated: spread({}) = {} > spread({}) = {}", h1, s1, h2, s2);
    }
}
