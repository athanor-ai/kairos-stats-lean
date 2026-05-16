//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

//! Property-based tests mirroring Lean theorems from `Pythia.Finance.Execution.TWAPSchedule`.

use proptest::prelude::*;
use pythia_execution_twap::TWAPSchedule;

proptest! {
    /// Lean: `participation_rate_bounded`
    /// For any valid schedule, participation rate = Q/(T*V) and is deterministic.
    #[test]
    fn prop_participation_rate_bounded(
        qty in 1.0f64..1_000_000.0,
        n in 1usize..100,
        horizon in 1.0f64..1000.0,
        volume in 1.0f64..10_000_000.0,
    ) {
        let rate_limit = qty / (horizon * volume) + 0.01; // set limit above actual
        let s = TWAPSchedule::new(qty, n, horizon, volume, rate_limit);
        prop_assert!(s.participation_rate() >= 0.0);
        prop_assert!(s.is_within_limit());
    }

    /// Lean: `longer_horizon_lower_rate`
    /// If T2 > T1, then Q/(T2*V) < Q/(T1*V).
    #[test]
    fn prop_longer_horizon_lower_rate(
        qty in 1.0f64..1_000_000.0,
        n in 1usize..100,
        t1 in 1.0f64..500.0,
        extra in 0.01f64..500.0,
        volume in 1.0f64..10_000_000.0,
    ) {
        let t2 = t1 + extra;
        let s = TWAPSchedule::new(qty, n, t1, volume, 1.0);
        prop_assert!(s.rate_at_horizon(t2) < s.rate_at_horizon(t1));
    }

    /// Lean: `schedule_completes`
    /// n slices of Q/n sums exactly to Q.
    #[test]
    fn prop_schedule_completes(
        qty in -1_000_000.0f64..1_000_000.0,
        n in 1usize..1000,
    ) {
        // Use a valid schedule (need positive horizon/volume for constructor)
        let s = TWAPSchedule::new(qty, n, 10.0, 1000.0, 1.0);
        let sum = s.schedule_sum();
        prop_assert!((sum - qty).abs() < 1e-8, "schedule_sum={} != qty={}", sum, qty);
    }

    /// Lean: `shortfall_nonneg`
    /// Shortfall is always >= 0 for any executed quantity.
    #[test]
    fn prop_shortfall_nonneg(
        qty in 0.0f64..1_000_000.0,
        n in 1usize..100,
        executed in 0.0f64..2_000_000.0,
    ) {
        let s = TWAPSchedule::new(qty, n, 10.0, 10000.0, 1.0);
        prop_assert!(s.shortfall(executed) >= 0.0);
    }
}
