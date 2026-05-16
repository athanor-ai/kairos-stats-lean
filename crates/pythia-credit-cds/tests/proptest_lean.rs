//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_credit_cds::CDS;

proptest! {
    /// Lean: `spread_hazard_recovery` — spread nonneg
    #[test]
    fn spread_nonneg(lam in 0.0f64..0.5, r in 0.0f64..1.0) {
        let cds = CDS::new(lam, r);
        prop_assert!(cds.spread() >= -1e-15);
    }

    /// Lean: `spread_recovery_monotone` — higher R → lower spread
    #[test]
    fn spread_mono_recovery(lam in 0.001f64..0.5, r1 in 0.0f64..0.5, extra in 0.0f64..0.5) {
        let r2 = (r1 + extra).min(1.0);
        let cds1 = CDS::new(lam, r1);
        let cds2 = CDS::new(lam, r2);
        prop_assert!(cds2.spread() <= cds1.spread() + 1e-12);
    }

    /// Lean: `survival_prob_pos`
    #[test]
    fn survival_pos(lam in 0.0f64..1.0, t in 0.0f64..30.0) {
        let cds = CDS::new(lam, 0.4);
        prop_assert!(cds.survival_prob(t) > 0.0);
    }

    /// Lean: `default_prob_bound` — P(default) ≤ 1
    #[test]
    fn default_bounded(lam in 0.0f64..1.0, t in 0.0f64..30.0) {
        let cds = CDS::new(lam, 0.4);
        let p = cds.default_prob(t);
        prop_assert!(p <= 1.0 + 1e-12);
        prop_assert!(p >= -1e-12);
    }
}
