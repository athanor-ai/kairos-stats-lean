//! Property-based tests for Kelly criterion with concavity.
//!
//! Provenance: verified against Lean spec `Pythia.Finance.KellyOptimal`.
//! Each proptest corresponds to a Lean theorem proven in the formal spec.

use proptest::prelude::*;
use pythia_portfolio_kelly2::*;

proptest! {
    /// Lean: `kellyFraction_even_odds` -- at b=1, f* = 2p - 1
    #[test]
    fn even_odds_formula(p in 0.0f64..1.0) {
        let f = kelly_fraction(p, 1.0).unwrap();
        let expected = 2.0 * p - 1.0;
        prop_assert!((f - expected).abs() < 1e-12);
    }

    /// Lean: `kellyFraction_nonneg`, `kellyFraction_le_one` --
    /// for p in [0,1] and b > 0 with positive edge, 0 <= f* <= 1
    #[test]
    fn kelly_in_unit_interval(
        p in 0.0f64..1.0,
        b in 0.01f64..100.0
    ) {
        if has_positive_edge(p, b) {
            let f = kelly_fraction(p, b).unwrap();
            prop_assert!(f >= -1e-12, "f* = {} should be nonneg for p={}, b={}", f, p, b);
            prop_assert!(f <= 1.0 + 1e-12, "f* = {} should be <= 1 for p={}, b={}", f, p, b);
        }
    }

    /// Lean: `kellyFraction_mono_p` -- f* is monotone increasing in p
    #[test]
    fn monotone_in_p(
        p1 in 0.0f64..1.0,
        p2 in 0.0f64..1.0,
        b in 0.01f64..100.0
    ) {
        let f1 = kelly_fraction(p1, b).unwrap();
        let f2 = kelly_fraction(p2, b).unwrap();
        if p1 <= p2 {
            prop_assert!(f1 <= f2 + 1e-12);
        } else {
            prop_assert!(f2 <= f1 + 1e-12);
        }
    }

    /// Lean: `overbetting_penalty_nonneg` -- (f - f*)^2 >= 0 always
    #[test]
    fn penalty_always_nonneg(
        f in -10.0f64..10.0,
        f_star in -10.0f64..10.0
    ) {
        prop_assert!(overbetting_penalty(f, f_star) >= 0.0);
    }

    /// Concavity: Kelly fraction maximizes growth rate (numerical check).
    /// For any f != f*, growth_rate(f) <= growth_rate(f*).
    #[test]
    fn kelly_maximizes_growth(
        p in 0.55f64..0.95,
        b in 0.5f64..5.0,
        delta in -0.15f64..0.15
    ) {
        let f_star = kelly_fraction(p, b).unwrap();
        // Only test if f_star is in a reasonable range for growth_rate computation
        if f_star > 0.01 && f_star < 0.99 {
            let f_test = f_star + delta;
            if f_test > 0.001 && f_test < 0.999 {
                if let (Some(g_star), Some(g_test)) = (growth_rate(p, f_star, b), growth_rate(p, f_test, b)) {
                    prop_assert!(g_star >= g_test - 1e-9,
                        "Growth at f*={} is {} but at f={} is {} (p={}, b={})",
                        f_star, g_star, f_test, g_test, p, b);
                }
            }
        }
    }
}
