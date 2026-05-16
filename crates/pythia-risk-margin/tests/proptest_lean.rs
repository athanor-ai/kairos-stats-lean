//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_risk_margin::*;

proptest! {
    /// Lean: `margin_ratio_decreases` — loss reduces margin ratio
    #[test]
    fn ratio_decreases(eq in 100.0f64..1000.0, loss in 1.0f64..100.0, pos in 500.0f64..5000.0) {
        prop_assert!(margin_ratio(eq - loss, pos) < margin_ratio(eq, pos) + 1e-10);
    }

    /// Lean: `liquidation_qty_nonneg`
    #[test]
    fn liq_nonneg(deficit in 0.0f64..10000.0, price in 1.0f64..500.0) {
        prop_assert!(liquidation_qty(deficit, price) >= 0.0);
    }

    /// Lean: `cascade_loss_nonneg`
    #[test]
    fn cascade_nonneg(slip in 0.0f64..0.1, qty in 0.0f64..10000.0) {
        prop_assert!(cascade_loss(slip, qty) >= -1e-15);
    }

    /// Lean: `margin_breach`
    #[test]
    fn breach_when_below(maint in 50.0f64..200.0, shortfall in 0.01f64..50.0) {
        prop_assert!(is_margin_breach(maint - shortfall, maint));
    }
}
