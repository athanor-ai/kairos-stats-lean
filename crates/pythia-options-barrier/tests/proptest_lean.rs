//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_options_barrier::*;

proptest! {
    /// Lean: `downOut_le_vanilla`
    #[test]
    fn barrier_dominance(s in -100.0f64..500.0, k in 0.01f64..500.0) {
        // For any alive flag, down_out_call <= vanilla_call
        prop_assert!(down_out_call(s, k, true) <= vanilla_call(s, k) + 1e-10);
        prop_assert!(down_out_call(s, k, false) <= vanilla_call(s, k) + 1e-10);
    }

    /// Lean: `downOut_nonneg`
    #[test]
    fn down_out_nonneg(s in -100.0f64..500.0, k in 0.01f64..500.0, alive in proptest::bool::ANY) {
        prop_assert!(down_out_call(s, k, alive) >= 0.0);
    }

    /// Lean: `knock_in_out_parity`
    #[test]
    fn knock_in_out_parity(s in 0.0f64..500.0, k in 0.01f64..500.0) {
        let vanilla = vanilla_call(s, k);
        let out = down_out_call(s, k, true);
        let in_payoff = knock_in_from_parity(vanilla, out);
        prop_assert!((in_payoff + out - vanilla).abs() < 1e-10);
    }

    /// Lean: `upOut_put_itm_at_barrier`
    #[test]
    fn up_out_at_barrier(k in 1.0f64..200.0, extra in 0.0f64..200.0) {
        let h = k + extra + 0.01; // H > K
        let s = h; // S >= H
        prop_assert_eq!(up_out_put(s, k, h), 0.0);
    }
}
