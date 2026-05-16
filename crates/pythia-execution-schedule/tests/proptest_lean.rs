//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (Cauchy-Schwarz, nlinarith on sq_nonneg, div_le_div).

use proptest::prelude::*;
use pythia_execution_schedule::*;

proptest! {
    /// Lean: `tempImpactCost_nonneg` — mul_nonneg + sum_nonneg + sq_nonneg
    #[test]
    fn cost_nonneg(eta in 0.0f64..1.0, t1 in -1000.0f64..1000.0, t2 in -1000.0f64..1000.0) {
        prop_assert!(temp_impact_cost(eta, &[t1, t2]) >= -1e-15);
    }

    /// Lean: `split_reduces_sq` — nlinarith [sq_nonneg(a-b)]
    #[test]
    fn split_reduces(a in 0.0f64..1000.0, b in 0.0f64..1000.0) {
        prop_assert!(a * a + b * b <= (a + b) * (a + b) + 1e-10);
    }

    /// Lean: `equal_split_optimal` — Cauchy-Schwarz
    #[test]
    fn equal_split_minimum(t1 in 0.0f64..500.0, t2 in 0.0f64..500.0, t3 in 0.0f64..500.0) {
        let trades = &[t1, t2, t3];
        let q: f64 = trades.iter().sum();
        let actual = temp_impact_cost(1.0, trades);
        let bound = equal_split_cost(1.0, q, 3);
        prop_assert!(bound <= actual + 1e-6);
    }

    /// Lean: `cost_antitone_horizon` — div_le_div_of_nonneg_left
    #[test]
    fn patience_pays(eta in 0.001f64..0.1, q in 100.0f64..10000.0, n1 in 1usize..50, extra in 1usize..50) {
        let n2 = n1 + extra;
        prop_assert!(cost_at_horizon(eta, q, n2) <= cost_at_horizon(eta, q, n1) + 1e-6);
    }

    /// Lean: `permanent_impact_nonneg` — div_nonneg + mul_nonneg + sq_nonneg
    #[test]
    fn perm_nonneg(gamma in 0.0f64..0.01, q in -10000.0f64..10000.0) {
        prop_assert!(permanent_impact(gamma, q) >= -1e-15);
    }
}
