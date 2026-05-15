use proptest::prelude::*;
use pythia_hft_slippage::{Fill, total_slippage, buy_impact};

proptest! {
    /// Lean: `slippage_zero_at_expected`
    #[test]
    fn zero_at_mid(price in 1.0f64..10000.0, qty in 1.0f64..10000.0) {
        let f = Fill { actual_price: price, expected_price: price, qty };
        prop_assert_eq!(f.slippage(), 0.0);
    }

    /// Lean: `slippage_bounded_by_half_spread`
    #[test]
    fn bounded_by_spread(
        mid in 50.0f64..200.0,
        offset in -0.05f64..0.05,
        qty in 1.0f64..1000.0
    ) {
        let f = Fill { actual_price: mid + offset, expected_price: mid, qty };
        prop_assert!(f.slippage().abs() <= 0.05 + 1e-10);
    }

    /// Lean: `slippage_sum`
    #[test]
    fn slippage_additive(
        a1 in 99.0f64..101.0, a2 in 99.0f64..101.0,
        e1 in 99.0f64..101.0, e2 in 99.0f64..101.0
    ) {
        let fills = vec![
            Fill { actual_price: a1, expected_price: e1, qty: 1.0 },
            Fill { actual_price: a2, expected_price: e2, qty: 1.0 },
        ];
        let total = total_slippage(&fills);
        let sum = (a1 - e1) + (a2 - e2);
        prop_assert!((total - sum).abs() < 1e-10);
    }

    /// Lean: `buy_impact_nonneg`
    #[test]
    fn buy_impact_nonneg(pre in 50.0f64..200.0, increase in 0.0f64..10.0) {
        prop_assert!(buy_impact(pre, pre + increase) >= 0.0);
    }
}
