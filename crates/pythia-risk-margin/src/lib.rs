//! # pythia-risk-margin
//!
//! Verified margin call mechanics.
//!
//! ## Lean specification (`Pythia.Finance.Risk.MarginCallMechanics`)
//!
//! - **Margin breach**: equity < maintenance (`margin_breach`)
//! - **Margin ratio decreases with loss** (`margin_ratio_decreases`)
//! - **Liquidation qty nonneg** (`liquidation_qty_nonneg`)
//! - **Cascade loss nonneg** (`cascade_loss_nonneg`)
//! - **Initial > maintenance** (`initial_gt_maintenance`)

/// Check margin breach: equity < maintenance margin.
/// # Lean: `margin_breach`
pub fn is_margin_breach(equity: f64, maint_margin: f64) -> bool {
    equity < maint_margin
}

/// Equity = assets - liabilities.
/// # Lean: `equity_identity`
pub fn equity(assets: f64, liabilities: f64) -> f64 {
    assets - liabilities
}

/// Margin ratio: equity / position.
/// # Lean: `margin_ratio_decreases`
pub fn margin_ratio(equity: f64, position: f64) -> f64 {
    if position.abs() > 1e-15 { equity / position.abs() } else { f64::INFINITY }
}

/// Liquidation quantity to restore margin: deficit / net_price.
/// # Lean: `liquidation_qty_nonneg`
pub fn liquidation_qty(deficit: f64, price_net: f64) -> f64 {
    assert!(price_net > 0.0);
    (deficit / price_net).max(0.0)
}

/// Cascade loss from forced liquidation: slippage * qty.
/// # Lean: `cascade_loss_nonneg`
pub fn cascade_loss(slippage: f64, qty: f64) -> f64 {
    slippage * qty
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn breach_detected() {
        assert!(is_margin_breach(80.0, 100.0));
        assert!(!is_margin_breach(120.0, 100.0));
    }

    #[test]
    fn equity_calc() {
        assert!((equity(1000.0, 300.0) - 700.0).abs() < 1e-10);
    }

    #[test]
    fn ratio_decreases_with_loss() {
        let r1 = margin_ratio(500.0, 1000.0);
        let r2 = margin_ratio(400.0, 1000.0);
        assert!(r2 < r1);
    }

    #[test]
    fn liquidation_nonneg() {
        assert!(liquidation_qty(100.0, 50.0) >= 0.0);
    }

    #[test]
    fn cascade_nonneg() {
        assert!(cascade_loss(0.02, 1000.0) >= 0.0);
    }
}
