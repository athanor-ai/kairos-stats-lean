//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_options_volsurface::*;

proptest! {
    /// Lean: `total_variance_nonneg` — σ²T ≥ 0
    #[test]
    fn total_var_nonneg(vol in 0.0f64..2.0, expiry in 0.0f64..10.0) {
        let p = VolPoint { strike: 100.0, expiry, implied_vol: vol };
        prop_assert!(p.total_variance() >= 0.0);
    }

    /// Lean: `butterfly_nonneg` — convex call prices pass
    #[test]
    fn butterfly_convex(c_mid in 1.0f64..20.0, convexity in 0.0f64..5.0, skew in -2.0f64..2.0) {
        let c_low = c_mid + convexity + skew;
        let c_high = c_mid + convexity - skew;
        prop_assert!(check_butterfly(c_low, c_mid, c_high));
    }

    /// Lean: `total_variance_mono` — monotone in time
    #[test]
    fn calendar_monotone(w1 in 0.0f64..1.0, increase in 0.0f64..1.0) {
        let w2 = w1 + increase;
        prop_assert!(check_calendar(w1, w2));
    }

    /// Lean: `svi_minimum_nonneg` — valid SVI params have nonneg minimum
    #[test]
    fn svi_valid(a in 0.01f64..0.5, b in 0.01f64..0.5, rho in -0.9f64..0.9, sigma in 0.01f64..1.0) {
        let svi = SviParams { a, b, rho, m: 0.0, sigma };
        if svi.minimum_variance() >= 0.0 {
            prop_assert!(svi.is_valid());
        }
    }

    /// Lean: `lee_moment_bound` — wing slopes within bound
    #[test]
    fn lee_within_bound(slope in 0.0f64..2.0) {
        prop_assert!(check_lee_bound(slope));
    }
}
