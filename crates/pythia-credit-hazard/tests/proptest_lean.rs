//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_credit_hazard::HazardModel;

proptest! {
    /// Lean: `survivalProb_pos` + `survivalProb_le_one`
    #[test]
    fn survival_in_01(h in 0.0f64..1.0, t in 0.0f64..30.0) {
        let m = HazardModel::new(h);
        let s = m.survival(t);
        prop_assert!(s > 0.0);
        prop_assert!(s <= 1.0 + 1e-12);
    }

    /// Lean: `survivalProb_antitone` — longer time → lower survival
    #[test]
    fn survival_antitone(h in 0.0f64..1.0, t1 in 0.0f64..15.0, extra in 0.0f64..15.0) {
        let m = HazardModel::new(h);
        prop_assert!(m.survival(t1 + extra) <= m.survival(t1) + 1e-12);
    }

    /// Lean: `defaultProb_nonneg` + `defaultProb_le_one`
    #[test]
    fn default_in_01(h in 0.0f64..1.0, t in 0.0f64..30.0) {
        let m = HazardModel::new(h);
        let p = m.default_prob(t);
        prop_assert!(p >= -1e-12);
        prop_assert!(p <= 1.0 + 1e-12);
    }

    /// Lean: `cds_spread_nonneg`
    #[test]
    fn cds_spread_nonneg(h in 0.0f64..0.5, r in 0.0f64..1.0) {
        let m = HazardModel::new(h);
        prop_assert!(m.cds_spread(r) >= -1e-15);
    }
}
