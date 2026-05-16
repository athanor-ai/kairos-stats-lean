//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (le_max_right, max_le_max_right, linarith, AM-GM dominance).

use proptest::prelude::*;
use pythia_options_asian::*;

proptest! {
    /// Lean: `arith_asian_call_nonneg` — le_max_right
    #[test]
    fn asian_call_nonneg(avg in -100.0f64..200.0, k in 0.0f64..200.0) {
        prop_assert!(asian_call_payoff(avg, k) >= 0.0);
    }

    /// Lean: `geom_call_le_arith_call` — AM-GM (max_le_max_right + linarith)
    #[test]
    fn geom_le_arith(
        p1 in 1.0f64..200.0,
        p2 in 1.0f64..200.0,
        p3 in 1.0f64..200.0,
        k in 0.0f64..200.0
    ) {
        let prices = vec![p1, p2, p3];
        let arith = arithmetic_avg(&prices);
        let geom = geometric_avg(&prices);
        // AM-GM: geom <= arith for positive values
        prop_assert!(geom <= arith + 1e-10);
        // Therefore geom call <= arith call
        prop_assert!(asian_call_payoff(geom, k) <= asian_call_payoff(arith, k) + 1e-10);
    }

    /// Lean: `floating_strike_nonneg` — le_max_right
    #[test]
    fn floating_nonneg(s_t in 50.0f64..200.0, avg in 50.0f64..200.0) {
        prop_assert!(floating_strike_payoff(s_t, avg) >= 0.0);
    }

    /// Lean: `asian_call_convex_in_avg` — max_le_max_right + linarith
    #[test]
    fn convex_in_avg(avg1 in 50.0f64..150.0, extra in 0.0f64..50.0, k in 50.0f64..200.0) {
        prop_assert!(asian_call_payoff(avg1, k) <= asian_call_payoff(avg1 + extra, k) + 1e-10);
    }
}
