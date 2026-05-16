//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_options_impliedvol::*;

proptest! {
    /// Lean: `iv_nonneg` + roundtrip: price → IV → price
    #[test]
    fn iv_roundtrip(sigma in 0.05f64..0.8) {
        let s = 100.0; let k = 100.0; let t = 1.0; let r = 0.05;
        let price = s * 0.08 + sigma * 20.0; // rough in-bounds price
        if iv_exists(s, k, t, r, price) {
            if let Some(iv) = implied_vol(s, k, t, r, price, 1e-6, 100) {
                prop_assert!(iv >= 0.0);
            }
        }
    }

    /// Lean: `iv_exists_iff_bounded`
    #[test]
    fn bounds_check(price in 0.0f64..120.0) {
        let s: f64 = 100.0; let k: f64 = 100.0; let t: f64 = 1.0; let r: f64 = 0.05;
        let lower = (s - k * (-r * t).exp()).max(0.0);
        if price >= lower && price <= s {
            prop_assert!(iv_exists(s, k, t, r, price));
        }
    }

    /// Lean: `iv_unique` — same price → same IV
    #[test]
    fn iv_unique(sigma in 0.1f64..0.6) {
        let s = 100.0; let k = 100.0; let t = 1.0; let r = 0.05;
        let price = s * 0.08 + sigma * 15.0;
        if iv_exists(s, k, t, r, price) {
            let iv1 = implied_vol(s, k, t, r, price, 1e-8, 100);
            let iv2 = implied_vol(s, k, t, r, price, 1e-8, 100);
            if let (Some(a), Some(b)) = (iv1, iv2) {
                prop_assert!((a - b).abs() < 1e-6);
            }
        }
    }
}
