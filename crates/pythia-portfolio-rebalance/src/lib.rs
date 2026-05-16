//! # pythia-portfolio-rebalance
//!
//! Verified portfolio rebalancing algebra.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.PortfolioRebalancing`)
//!
//! - **Zero trade iff weights match** (`tradeFraction_zero_iff`)
//! - **Trade fraction antisymmetric** (`tradeFraction_antisymm`)
//! - **Drifted wealth at equal returns** = 1+r (`driftedWealth_at_equal_returns`)
//! - **Drifted wealth positive** under standard conditions (`driftedWealth_pos`)
//! - **Drifted wealth linear in weight** (`driftedWealth_linear`)

/// Trade fraction needed to rebalance from current to target weight.
///
/// # Lean: `tradeFraction`
#[inline(always)]
pub fn trade_fraction(w_target: f64, w_current: f64) -> f64 {
    w_target - w_current
}

/// Total portfolio wealth after returns, given initial weight w on asset 1
/// with return r1 and weight (1-w) on asset 2 with return r2.
/// Normalized to initial wealth = 1.
///
/// # Lean: `driftedWealth`
#[inline(always)]
pub fn drifted_wealth(w: f64, r1: f64, r2: f64) -> f64 {
    w * (1.0 + r1) + (1.0 - w) * (1.0 + r2)
}

/// Drifted weight of asset 1 after returns.
/// w_drifted = w * (1+r1) / driftedWealth(w, r1, r2)
///
/// Requires drifted_wealth > 0.
pub fn drifted_weight(w: f64, r1: f64, r2: f64) -> f64 {
    let total = drifted_wealth(w, r1, r2);
    assert!(total > 0.0, "drifted wealth must be positive");
    w * (1.0 + r1) / total
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trade_fraction_zero_when_equal() {
        assert_eq!(trade_fraction(0.6, 0.6), 0.0);
    }

    #[test]
    fn trade_fraction_antisymmetric() {
        let tf1 = trade_fraction(0.6, 0.4);
        let tf2 = trade_fraction(0.4, 0.6);
        assert!((tf1 + tf2).abs() < 1e-10);
    }

    #[test]
    fn drifted_wealth_equal_returns() {
        let w = 0.7;
        let r = 0.05;
        let dw = drifted_wealth(w, r, r);
        assert!((dw - (1.0 + r)).abs() < 1e-10);
    }

    #[test]
    fn drifted_wealth_positive() {
        // w in [0,1], r1 > -1, r2 > -1
        assert!(drifted_wealth(0.5, 0.1, 0.2) > 0.0);
        assert!(drifted_wealth(0.0, 0.1, -0.5) > 0.0);
        assert!(drifted_wealth(1.0, -0.5, 0.3) > 0.0);
    }

    #[test]
    fn drifted_wealth_linear_form() {
        let w = 0.4;
        let r1 = 0.1;
        let r2 = 0.05;
        let actual = drifted_wealth(w, r1, r2);
        let linear = (1.0 + r2) + w * (r1 - r2);
        assert!((actual - linear).abs() < 1e-10);
    }

    #[test]
    fn drifted_weight_no_change_at_equal_returns() {
        let w = 0.6;
        let r = 0.03;
        let dw = drifted_weight(w, r, r);
        assert!((dw - w).abs() < 1e-10);
    }
}
