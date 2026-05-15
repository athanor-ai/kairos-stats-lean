//! Property tests for risk-neutral pricing, mirroring Lean spec `Pythia.Finance.RiskNeutralMeasure`.

use proptest::prelude::*;
use pythia_finance_rnpricing::{RnPricer, payoff_add, payoff_smul};

/// Strategy: generate a valid 3-state pricer with random probabilities summing to 1.
fn arb_pricer() -> impl Strategy<Value = RnPricer> {
    (0.01f64..0.98, 0.01f64..0.98, 0.5f64..1.0).prop_filter_map(
        "probs must sum to ~1",
        |(a, b, disc)| {
            let c = 1.0 - a - b;
            if c > 0.01 {
                RnPricer::new(vec![a, b, c], disc)
            } else {
                None
            }
        },
    )
}

fn arb_payoff3() -> impl Strategy<Value = Vec<f64>> {
    prop::collection::vec(0.0f64..100.0, 3..=3)
}

proptest! {
    /// Lean: `rnPrice_add` — price(X + Y) = price(X) + price(Y).
    #[test]
    fn prop_price_add(
        pricer in arb_pricer(),
        x in arb_payoff3(),
        y in arb_payoff3(),
    ) {
        let xy = payoff_add(&x, &y).unwrap();
        let lhs = pricer.price(&xy).unwrap();
        let rhs = pricer.price(&x).unwrap() + pricer.price(&y).unwrap();
        prop_assert!((lhs - rhs).abs() < 1e-10, "linearity: |{} - {}| = {}", lhs, rhs, (lhs - rhs).abs());
    }

    /// Lean: `rnPrice_smul` — price(c * X) = c * price(X).
    #[test]
    fn prop_price_smul(
        pricer in arb_pricer(),
        x in arb_payoff3(),
        c in -10.0f64..10.0,
    ) {
        let cx = payoff_smul(c, &x);
        let lhs = pricer.price(&cx).unwrap();
        let rhs = c * pricer.price(&x).unwrap();
        prop_assert!((lhs - rhs).abs() < 1e-9, "homogeneity: |{} - {}| = {}", lhs, rhs, (lhs - rhs).abs());
    }

    /// Lean: `rnPrice_mono` — if X_i >= Y_i for all i, then price(X) >= price(Y).
    #[test]
    fn prop_price_mono(
        pricer in arb_pricer(),
        y in arb_payoff3(),
        spread in prop::collection::vec(0.0f64..50.0, 3..=3),
    ) {
        let x: Vec<f64> = y.iter().zip(spread.iter()).map(|(yi, si)| yi + si).collect();
        let px = pricer.price(&x).unwrap();
        let py = pricer.price(&y).unwrap();
        prop_assert!(px >= py - 1e-12, "monotonicity: {} < {}", px, py);
    }

    /// Lean: `rnPrice_nonneg` — nonneg payoff => nonneg price.
    #[test]
    fn prop_price_nonneg(
        pricer in arb_pricer(),
        x in arb_payoff3(),
    ) {
        let px = pricer.price(&x).unwrap();
        prop_assert!(px >= -1e-12, "nonneg violated: {}", px);
    }
}
