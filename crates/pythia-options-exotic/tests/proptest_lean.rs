use proptest::prelude::*;
use pythia_options_exotic::*;

proptest! {
    /// Lean: `straddle_nonneg`
    #[test]
    fn straddle_nonneg(call in 0.0f64..100.0, put in 0.0f64..100.0) {
        prop_assert!(straddle_value(call, put) >= 0.0);
    }

    /// Lean: `knockin_knockout_parity`
    #[test]
    fn barrier_parity(ki in 0.0f64..50.0, ko in 0.0f64..50.0) {
        let vanilla = ki + ko;
        prop_assert!(check_barrier_parity(ki, ko, vanilla, 1e-10));
    }

    /// Lean: `digital_bounded`
    #[test]
    fn digital_in_01(price in 0.0f64..1.0) {
        prop_assert!(check_digital_bounded(price));
    }

    /// Lean: `knockin_le_vanilla` + `lookback_ge_vanilla`
    #[test]
    fn ordering(vanilla in 1.0f64..100.0, ki_frac in 0.0f64..1.0, lb_extra in 0.0f64..50.0) {
        let ki = vanilla * ki_frac;
        let lb = vanilla + lb_extra;
        prop_assert!(check_knockin_bound(ki, vanilla));
        prop_assert!(check_lookback_bound(lb, vanilla));
    }
}
