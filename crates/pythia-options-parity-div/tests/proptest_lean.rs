//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_options_parity_div::*;

proptest! {
    /// Lean: `put_call_parity_dividend` -- C - P = S*exp(-qT) - K*exp(-rT) for all params
    #[test]
    fn parity_identity_with_dividends(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        t in 0.01f64..5.0,
        r in 0.0f64..0.2,
        q in 0.0f64..0.1
    ) {
        let c = call_payoff_div(s, k, t, r, q);
        let p = put_payoff_div(s, k, t, r, q);
        prop_assert!(check_parity_div(c, p, s, k, t, r, q, 1e-10));
    }

    /// Lean: `callPayoffDiv`, `putPayoffDiv` -- payoffs are nonnegative
    #[test]
    fn payoff_nonnegativity(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        t in 0.0f64..5.0,
        r in 0.0f64..0.2,
        q in 0.0f64..0.1
    ) {
        prop_assert!(call_payoff_div(s, k, t, r, q) >= 0.0);
        prop_assert!(put_payoff_div(s, k, t, r, q) >= 0.0);
    }

    /// Lean: `put_call_parity_dividend` with q=0 -- reduces to no-dividend parity
    /// At q=0: C - P = S - K*exp(-rT)
    #[test]
    fn zero_dividend_recovers_standard(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        t in 0.01f64..5.0,
        r in 0.0f64..0.2
    ) {
        let c = call_payoff_div(s, k, t, r, 0.0);
        let p = put_payoff_div(s, k, t, r, 0.0);
        let diff = c - p;
        let standard_rhs = s - k * (-r * t).exp();
        prop_assert!((diff - standard_rhs).abs() < 1e-10,
            "q=0 should recover standard parity: got {}, expected {}", diff, standard_rhs);
    }

    /// Lean: `put_call_parity_dividend` at T=0 -- C - P = S - K exactly
    #[test]
    fn zero_time_specialization(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        r in 0.0f64..0.2,
        q in 0.0f64..0.1
    ) {
        let c = call_payoff_div(s, k, 0.0, r, q);
        let p = put_payoff_div(s, k, 0.0, r, q);
        let diff = c - p;
        prop_assert!((diff - (s - k)).abs() < 1e-12,
            "At T=0, C-P should equal S-K: got {}, expected {}", diff, s - k);
    }
}
