use proptest::prelude::*;
use pythia_finance_execution::Schedule;

proptest! {
    /// Lean: `twapSchedule_sum` — TWAP sums to Q
    #[test]
    fn twap_sums_to_q(q in 1.0f64..100000.0, n in 1usize..100) {
        let s = Schedule::twap(q, n);
        prop_assert!((s.total_qty() - q).abs() < 1e-6);
    }

    /// Lean: `twapIsOptimal` — any schedule costs ≥ TWAP
    #[test]
    fn twap_optimality(
        t1 in 0.0f64..1000.0, t2 in 0.0f64..1000.0, t3 in 0.0f64..1000.0,
        eta in 0.0f64..1.0
    ) {
        let s = Schedule { trades: vec![t1, t2, t3] };
        prop_assert!(s.is_at_least_twap_cost(eta));
    }

    /// Lean: `sum_sq_ge_sq_sum_div` — Cauchy-Schwarz: Q² ≤ n * Σ x²
    #[test]
    fn cauchy_schwarz(t1 in -100.0f64..100.0, t2 in -100.0f64..100.0, t3 in -100.0f64..100.0) {
        let q = t1 + t2 + t3;
        let sum_sq = t1*t1 + t2*t2 + t3*t3;
        prop_assert!(q * q <= 3.0 * sum_sq + 1e-10);
    }
}
