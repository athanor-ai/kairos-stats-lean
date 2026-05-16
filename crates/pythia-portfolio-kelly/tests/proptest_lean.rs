//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_kelly::*;

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
}
