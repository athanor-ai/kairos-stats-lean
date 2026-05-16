//! Provenance: VERIFIED — the Lean proofs in
//! `Pythia.Finance.FixedIncome.ConvexityDuration` use `ring` to close all three
//! theorems (`bondLogPrice_at_zero_y`, `bondLogPrice_zero_convexity`,
//! `bondLogPrice_linear_logB`). These are non-tautological algebraic identities
//! verified by Lean's ring solver.

use proptest::prelude::*;
use pythia_fixedincome_duration::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `bondLogPrice_at_zero_y`
    /// At y = 0, bondLogPrice(logB, D, C, 0) == logB.
    #[test]
    fn prop_at_zero_yield(
        log_b in -100.0..100.0f64,
        d in -100.0..100.0f64,
        c in -100.0..100.0f64,
    ) {
        let result = bond_log_price(log_b, d, c, 0.0);
        prop_assert!((result - log_b).abs() < EPS,
            "at-zero-yield failed: result={}, logB={}", result, log_b);
    }

    /// Lean: `bondLogPrice_zero_convexity`
    /// With C = 0, bondLogPrice(logB, D, 0, y) == logB - D*y.
    #[test]
    fn prop_zero_convexity(
        log_b in -100.0..100.0f64,
        d in -100.0..100.0f64,
        y in -10.0..10.0f64,
    ) {
        let result = bond_log_price(log_b, d, 0.0, y);
        let expected = log_b - d * y;
        prop_assert!((result - expected).abs() < EPS,
            "zero-convexity failed: result={}, expected={}", result, expected);
    }

    /// Lean: `bondLogPrice_linear_logB`
    /// bondLogPrice(logB + delta, D, C, y) == bondLogPrice(logB, D, C, y) + delta.
    #[test]
    fn prop_linear_logb(
        log_b in -100.0..100.0f64,
        delta in -100.0..100.0f64,
        d in -100.0..100.0f64,
        c in -100.0..100.0f64,
        y in -10.0..10.0f64,
    ) {
        let base = bond_log_price(log_b, d, c, y);
        let shifted = bond_log_price_shifted(log_b, delta, d, c, y);
        prop_assert!((shifted - (base + delta)).abs() < EPS,
            "linearity failed: shifted={}, base+delta={}", shifted, base + delta);
    }

    /// Structural: convexity always adds a non-negative term for C >= 0.
    /// bondLogPrice(logB, D, C, y) >= bondLogPrice(logB, D, 0, y) when C >= 0.
    #[test]
    fn prop_convexity_nonneg_contribution(
        log_b in -100.0..100.0f64,
        d in -100.0..100.0f64,
        c in 0.0..100.0f64,
        y in -10.0..10.0f64,
    ) {
        let with_c = bond_log_price(log_b, d, c, y);
        let without_c = bond_log_price(log_b, d, 0.0, y);
        prop_assert!(with_c >= without_c - EPS,
            "convexity contribution negative: with_c={}, without_c={}", with_c, without_c);
    }
}
