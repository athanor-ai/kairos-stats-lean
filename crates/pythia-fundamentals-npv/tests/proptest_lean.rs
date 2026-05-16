//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content.

use proptest::prelude::*;
use pythia_fundamentals_npv::*;

proptest! {
    /// Lean: `netPresentValue_zero_cf` — zero cashflows give zero NPV
    #[test]
    fn zero_cf(r in 0.0f64..0.3, t1 in 0.0f64..10.0, t2 in 0.0f64..10.0, t3 in 0.0f64..10.0) {
        let cf = [0.0, 0.0, 0.0];
        let t = [t1, t2, t3];
        prop_assert!((net_present_value(&cf, &t, r)).abs() < 1e-15);
    }

    /// Lean: `netPresentValue_linear` — scalar linearity
    #[test]
    fn linearity(c1 in 0.0f64..1000.0, c2 in 0.0f64..1000.0, t1 in 0.0f64..10.0, t2 in 0.0f64..10.0, r in 0.0f64..0.2, alpha in 0.1f64..5.0) {
        let cf = [c1, c2];
        let t = [t1, t2];
        let scaled_cf = [alpha * c1, alpha * c2];
        let npv_base = net_present_value(&cf, &t, r);
        let npv_scaled = net_present_value(&scaled_cf, &t, r);
        prop_assert!((npv_scaled - alpha * npv_base).abs() < 1e-8);
    }

    /// Lean: `netPresentValue_additive` — additivity
    #[test]
    fn additivity(c1 in 0.0f64..500.0, c2 in 0.0f64..500.0, d1 in 0.0f64..500.0, d2 in 0.0f64..500.0, t1 in 0.0f64..10.0, t2 in 0.0f64..10.0, r in 0.0f64..0.2) {
        let cf1 = [c1, c2];
        let cf2 = [d1, d2];
        let combined = [c1 + d1, c2 + d2];
        let t = [t1, t2];
        let npv1 = net_present_value(&cf1, &t, r);
        let npv2 = net_present_value(&cf2, &t, r);
        let npv_combined = net_present_value(&combined, &t, r);
        prop_assert!((npv_combined - (npv1 + npv2)).abs() < 1e-8);
    }

    /// Lean: `netPresentValue_antitone_rate` — higher rate, lower NPV (nonneg cf, nonneg t)
    #[test]
    fn antitone_rate(c1 in 0.0f64..500.0, c2 in 0.0f64..500.0, t1 in 0.0f64..10.0, t2 in 0.0f64..10.0, r1 in 0.0f64..0.1, extra in 0.0f64..0.2) {
        let r2 = r1 + extra;
        let cf = [c1, c2];
        let t = [t1, t2];
        let npv1 = net_present_value(&cf, &t, r1);
        let npv2 = net_present_value(&cf, &t, r2);
        prop_assert!(npv2 <= npv1 + 1e-10);
    }
}
