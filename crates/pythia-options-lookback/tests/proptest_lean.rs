//! Provenance: VERIFIED — the Lean proofs in `Pythia.Finance.Options.LookbackOption`
//! use `linarith`, `rcases`, and `ring` to establish these properties non-tautologically.
//! These proptests exercise the same algebraic invariants in the Rust implementation.

use proptest::prelude::*;
use pythia_options_lookback::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `lookback_call_nonneg`
    /// When path_min <= S_T, the lookback call payoff is non-negative.
    #[test]
    fn prop_call_nonneg(s_t in 0.0f64..1000.0, delta in 0.0f64..500.0) {
        let path_min = s_t - delta; // ensures path_min <= s_t
        prop_assert!(lookback_call_payoff(s_t, path_min) >= -EPS);
    }

    /// Lean: `lookback_dominates_vanilla`
    /// lookback_call >= max(S_T - S_0, 0) when path_min <= S_0 and path_min <= S_T.
    #[test]
    fn prop_dominates_vanilla(s_t in 0.0f64..500.0, s_0 in 0.0f64..500.0, gap in 0.0f64..200.0) {
        let path_min = s_0.min(s_t) - gap; // ensures path_min <= S_0 and path_min <= S_T
        let lookback = lookback_call_payoff(s_t, path_min);
        let vanilla = vanilla_call(s_t, s_0);
        prop_assert!(lookback >= vanilla - EPS,
            "dominance violated: lookback={}, vanilla={}", lookback, vanilla);
    }

    /// Lean: `lookback_put_nonneg`
    /// When S_T <= path_max, the lookback put payoff is non-negative.
    #[test]
    fn prop_put_nonneg(s_t in 0.0f64..1000.0, delta in 0.0f64..500.0) {
        let path_max = s_t + delta; // ensures S_T <= path_max
        prop_assert!(lookback_put_payoff(path_max, s_t) >= -EPS);
    }

    /// Lean: `lookback_straddle`
    /// lookback_call + lookback_put = path_max - path_min (the range).
    #[test]
    fn prop_straddle_is_range(s_t in 0.0f64..500.0, min_gap in 0.0f64..200.0, max_gap in 0.0f64..200.0) {
        let path_min = s_t - min_gap;
        let path_max = s_t + max_gap;
        let straddle = lookback_straddle(s_t, path_min, path_max);
        let range = path_max - path_min;
        prop_assert!((straddle - range).abs() < EPS,
            "straddle={}, range={}", straddle, range);
    }
}
