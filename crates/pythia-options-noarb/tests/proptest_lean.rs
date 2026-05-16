//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_options_noarb::*;

proptest! {
    /// Lean: `call_lower_bound` -- C = max(S - K_disc, 0) satisfies its own bound
    #[test]
    fn call_lower_bound_self_consistent(
        s in 1.0f64..500.0,
        k in 1.0f64..500.0,
        r in 0.0f64..0.2,
        t in 0.01f64..5.0
    ) {
        let bound = call_lower_bound(s, k, r, t);
        // The bound itself trivially satisfies the check
        prop_assert!(check_call_lower_bound(bound, s, k, r, t, 1e-10));
        // And the bound is always nonneg
        prop_assert!(bound >= 0.0);
    }

    /// Lean: `butterfly_nonneg` -- convex call prices produce nonneg butterfly
    /// For equally spaced strikes, butterfly = C1 - 2*C2 + C3 >= 0 when
    /// C2 <= (C1 + C3) / 2 (convexity). We construct C2 at or below the midpoint.
    #[test]
    fn butterfly_nonneg_from_convex(
        c1 in 0.0f64..100.0,
        c3 in 0.0f64..100.0,
        frac in 0.0f64..1.0
    ) {
        // c2 is at most the midpoint (convexity condition for butterfly)
        let midpoint = (c1 + c3) / 2.0;
        let c2 = frac * midpoint;
        // butterfly = c1 - 2*c2 + c3 >= 0
        prop_assert!(check_butterfly_nonneg(c1, c2, c3, 1e-10));
    }

    /// Lean: `call_spread_nonneg`, `call_spread_bounded` -- spread in [0, K2_disc - K1_disc]
    /// We generate two call prices from the lower bound function (monotone decreasing in K).
    #[test]
    fn call_spread_from_lower_bound(
        s in 50.0f64..200.0,
        k1 in 1.0f64..150.0,
        k_gap in 0.01f64..100.0,
        r in 0.0f64..0.15,
        t in 0.01f64..3.0
    ) {
        let k2 = k1 + k_gap;
        let c1 = call_lower_bound(s, k1, r, t);
        let c2 = call_lower_bound(s, k2, r, t);
        // c1 >= c2 (lower strike call is worth more)
        prop_assert!(check_call_spread_nonneg(c1, c2, 1e-10));
    }

    /// Lean: `law_of_one_price` -- reflexivity: every price equals itself
    #[test]
    fn law_of_one_price_reflexive(p in -1000.0f64..1000.0) {
        prop_assert!(check_law_of_one_price(p, p, 1e-12));
    }
}
