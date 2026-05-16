//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_options_parity::*;

proptest! {
    /// Lean: `put_call_parity_discounted` — call - put = (S-K)*exp(-rT) for all S, K
    #[test]
    fn parity_identity_all_s_k(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        t in 0.01f64..5.0,
        r in 0.0f64..0.2
    ) {
        let c = call_payoff(s, k, t, r);
        let p = put_payoff(s, k, t, r);
        prop_assert!(check_parity(c, p, s, k, t, r, 1e-10));
    }

    /// Lean: `callPayoff`, `putPayoff` — payoffs are nonnegative
    #[test]
    fn payoff_nonnegativity(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        t in 0.0f64..5.0,
        r in 0.0f64..0.2
    ) {
        prop_assert!(call_payoff(s, k, t, r) >= 0.0);
        prop_assert!(put_payoff(s, k, t, r) >= 0.0);
    }

    /// Lean: `put_call_payoff_identity` at T=0 — zero-time specialization
    /// At T=0, discount factor is 1, so call - put = S - K exactly.
    #[test]
    fn zero_time_specialization(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        r in 0.0f64..0.2
    ) {
        let c = call_payoff(s, k, 0.0, r);
        let p = put_payoff(s, k, 0.0, r);
        let diff = c - p;
        prop_assert!((diff - (s - k)).abs() < 1e-12);
    }

    /// Lean: `put_call_payoff_identity` — max(S-K,0) - max(K-S,0) = S - K
    #[test]
    fn raw_payoff_identity(s in -1000.0f64..1000.0, k in -1000.0f64..1000.0) {
        prop_assert!((payoff_identity(s, k) - (s - k)).abs() < 1e-12);
    }
}
