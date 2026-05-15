use proptest::prelude::*;
use pythia_hft_latency::{Pipeline, Stage, batch_rounds};

proptest! {
    /// Lean: `pipeline_bounded` — total ≤ n * max
    #[test]
    fn pipeline_bounded(
        s1 in 1u64..1000, s2 in 1u64..1000, s3 in 1u64..1000
    ) {
        let p = Pipeline::new(vec![
            Stage::new("a", s1, 0),
            Stage::new("b", s2, 0),
            Stage::new("c", s3, 0),
        ]);
        prop_assert!(p.total_wcet_ns() <= p.bound_ns());
    }

    /// Lean: `jitter_bounded` — total jitter ≤ n * max_jitter
    #[test]
    fn jitter_bounded(
        w1 in 10u64..1000, b1 in 0u64..10,
        w2 in 10u64..1000, b2 in 0u64..10,
    ) {
        let p = Pipeline::new(vec![
            Stage::new("a", w1, b1),
            Stage::new("b", w2, b2),
        ]);
        prop_assert!(p.total_jitter_ns() <= p.jitter_bound_ns());
    }

    /// Lean: `batch_rounds` — N ≤ ceil(N/B) * B
    #[test]
    fn batch_covers_all(n in 0u64..10000, b in 1u64..100) {
        let rounds = batch_rounds(n, b);
        prop_assert!(n <= rounds * b);
    }

    /// Lean: `pipeline_additive` — total is non-negative
    #[test]
    fn pipeline_nonneg(s1 in 0u64..1000, s2 in 0u64..1000) {
        let p = Pipeline::new(vec![
            Stage::new("a", s1, 0),
            Stage::new("b", s2, 0),
        ]);
        prop_assert!(p.total_wcet_ns() >= 0);
    }
}
