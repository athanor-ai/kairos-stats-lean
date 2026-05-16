//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_hft_marketmaking::{AvellanedaStoikov, Quote};

proptest! {
    /// Lean: `spread_profit_nonneg`
    #[test]
    fn spread_profit_nonneg(bid in 50.0f64..150.0, spread in 0.0f64..1.0, qty in 0.0f64..10000.0) {
        let q = Quote { bid, ask: bid + spread };
        prop_assert!(q.round_trip_profit(qty) >= 0.0);
    }

    /// Lean: `inventory_risk_nonneg`
    #[test]
    fn inventory_risk_nonneg(q in -10000.0f64..10000.0, sigma in 0.0f64..1.0) {
        let mm = AvellanedaStoikov::new(0.1, sigma);
        prop_assert!(mm.inventory_risk(q) >= 0.0);
    }

    /// Lean: `inventory_risk_mono` — larger |q| → more risk
    #[test]
    fn inventory_risk_mono(q1 in 0.0f64..1000.0, extra in 0.0f64..1000.0, sigma in 0.01f64..1.0) {
        let mm = AvellanedaStoikov::new(0.1, sigma);
        let q2 = q1 + extra;
        prop_assert!(mm.inventory_risk(q1) <= mm.inventory_risk(q2) + 1e-10);
    }

    /// Lean: `spread_widens_with_vol`
    #[test]
    fn spread_widens_with_vol(s1 in 0.0f64..0.5, extra in 0.0f64..0.5, k in 0.0f64..10.0) {
        let s2 = s1 + extra;
        let mm1 = AvellanedaStoikov::new(0.1, s1);
        let mm2 = AvellanedaStoikov::new(0.1, s2);
        prop_assert!(mm1.half_spread(k) <= mm2.half_spread(k) + 1e-10);
    }

    /// Lean: `inventory_skew_direction` — long skews down
    #[test]
    fn long_inventory_skews_down(mid in 50.0f64..200.0, q in 0.01f64..10000.0, gamma in 0.001f64..1.0) {
        let mm = AvellanedaStoikov::new(gamma, 0.02);
        prop_assert!(mm.adjusted_mid(mid, q) < mid);
    }

    /// Lean: `round_trip_profitable`
    #[test]
    fn round_trip_profitable(spread in 0.02f64..1.0, fee in 0.001f64..0.005, qty in 1.0f64..10000.0) {
        let q = Quote { bid: 100.0, ask: 100.0 + spread };
        if spread > 2.0 * fee {
            prop_assert!(q.net_pnl(qty, fee) > 0.0);
        }
    }

    /// Lean: `symmetric_spread`
    #[test]
    fn symmetric_spread(mid in 50.0f64..200.0, k in 0.1f64..5.0, sigma in 0.01f64..0.5) {
        let mm = AvellanedaStoikov::new(0.1, sigma);
        let q = mm.quote(mid, 0.0, k);
        let expected = 2.0 * mm.half_spread(k);
        prop_assert!((q.spread() - expected).abs() < 1e-10);
    }
}
