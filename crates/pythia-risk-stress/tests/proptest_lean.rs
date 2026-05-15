//! Property tests for stress testing, mirroring Lean spec
//! `Pythia.Finance.Risk.StressTest`.

use proptest::prelude::*;
use pythia_risk_stress::{capital_surplus, long_down_loss, StressScenario};

/// Generate an arbitrary stress scenario with `n` positions.
fn arb_scenario(n: usize) -> impl Strategy<Value = StressScenario> {
    proptest::collection::vec(-1000.0f64..1000.0, n).prop_map(StressScenario::new)
}

proptest! {
    /// Lean: `diversification_in_stress` -- triangle inequality always holds.
    #[test]
    fn prop_diversification_triangle(s in arb_scenario(8)) {
        prop_assert!(
            s.total_pnl().abs() <= s.sum_abs_pnl() + 1e-10,
            "|sum| = {} > sum(|.|) = {}",
            s.total_pnl().abs(),
            s.sum_abs_pnl()
        );
    }

    /// Lean: `worst_case_bounded` -- total <= n * max when all entries <= max.
    #[test]
    fn prop_worst_case_bounded(s in arb_scenario(6)) {
        let max_loss = s.pnls.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let total = s.total_pnl();
        let bound = s.n() as f64 * max_loss;
        prop_assert!(total <= bound + 1e-10, "total {} > bound {}", total, bound);
    }

    /// Lean: `long_portfolio_down_loss` -- positive * positive > 0.
    #[test]
    fn prop_long_down_loss_positive(
        position in 0.01f64..1e6,
        drop in 0.01f64..1.0,
    ) {
        let loss = long_down_loss(position, drop);
        prop_assert!(loss > 0.0, "loss {} not positive", loss);
    }

    /// Lean: `capital_adequate` -- capital >= worst_loss implies nonneg surplus.
    #[test]
    fn prop_capital_adequate(
        worst_loss in 0.0f64..1e6,
        excess in 0.0f64..1e6,
    ) {
        let capital = worst_loss + excess;
        let surplus = capital_surplus(capital, worst_loss);
        prop_assert!(surplus >= -1e-10, "surplus {} < 0", surplus);
    }
}
