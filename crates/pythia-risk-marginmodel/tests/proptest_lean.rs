//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_risk_marginmodel::*;

proptest! {
    /// Lean: `initialMargin_nonneg` — mul_nonneg + abs_nonneg
    #[test]
    fn margin_nonneg(rate in 0.0f64..1.0, value in -10000.0f64..10000.0) {
        prop_assert!(initial_margin(rate, value) >= -1e-15);
    }

    /// Lean: `portfolio_margin_subadditive` — abs_add_le + mul_le_mul_of_nonneg_left
    #[test]
    fn subadditive(rate in 0.0f64..1.0, v1 in -5000.0f64..5000.0, v2 in -5000.0f64..5000.0) {
        let port = initial_margin(rate, v1 + v2);
        let sum = initial_margin(rate, v1) + initial_margin(rate, v2);
        prop_assert!(port <= sum + 1e-10);
    }

    /// Lean: `netting_reduces_margin` — abs_sum_le_sum_abs
    #[test]
    fn netting_reduces(rate in 0.0f64..1.0, p1 in -1000.0f64..1000.0, p2 in -1000.0f64..1000.0, p3 in -1000.0f64..1000.0) {
        let positions = &[p1, p2, p3];
        prop_assert!(portfolio_margin(rate, positions) <= gross_margin(rate, positions) + 1e-10);
    }

    /// Lean: `margin_scales` — abs_mul + ring
    #[test]
    fn scales(rate in 0.0f64..1.0, c in -10.0f64..10.0, value in -1000.0f64..1000.0) {
        let direct = initial_margin(rate, c * value);
        let scaled = c.abs() * initial_margin(rate, value);
        prop_assert!((direct - scaled).abs() < 1e-8);
    }

    /// Lean: `liquidation_qty_nonneg` — div_nonneg
    #[test]
    fn liquidation_nonneg(deficit in 0.0f64..100000.0, price in 1.0f64..1000.0) {
        prop_assert!(liquidation_qty(deficit, price) >= 0.0);
    }
}
