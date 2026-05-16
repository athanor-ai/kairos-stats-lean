//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_execution_router::*;

proptest! {
    /// Lean: `price_improvement_nonneg`
    #[test]
    fn improvement_nonneg(nbbo in 100.0f64..110.0, discount in 0.0f64..1.0) {
        prop_assert!(price_improvement(nbbo, nbbo - discount) >= -1e-12);
    }

    /// Lean: `wafp_between`
    #[test]
    fn wafp_bounded(p1 in 99.0f64..101.0, p2 in 99.0f64..101.0, q1 in 1.0f64..1000.0, q2 in 1.0f64..1000.0) {
        let w = wafp(&[(p1, q1), (p2, q2)]);
        let lo = p1.min(p2);
        let hi = p1.max(p2);
        prop_assert!(w >= lo - 1e-10);
        prop_assert!(w <= hi + 1e-10);
    }

    /// Lean: `routing_preserves_qty`
    #[test]
    fn qty_preserved(q1 in 0.0f64..500.0, q2 in 0.0f64..500.0, q3 in 0.0f64..500.0) {
        let total = q1 + q2 + q3;
        prop_assert!(check_qty_preserved(&[q1, q2, q3], total, 1e-10));
    }

    /// Lean: `best_price_le_all`
    #[test]
    fn best_le_all(p1 in 99.0f64..101.0, p2 in 99.0f64..101.0, p3 in 99.0f64..101.0) {
        let venues = vec![
            Venue { price: p1, available: 100.0, fee: 0.0 },
            Venue { price: p2, available: 100.0, fee: 0.0 },
            Venue { price: p3, available: 100.0, fee: 0.0 },
        ];
        if let Some(best_idx) = best_venue(&venues) {
            let best_cost = venues[best_idx].total_cost();
            for v in &venues {
                prop_assert!(best_cost <= v.total_cost() + 1e-12);
            }
        }
    }
}
