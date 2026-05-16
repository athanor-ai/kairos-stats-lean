//! # pythia-options-volpnl
//!
//! Verified volatility trading PnL chain.
//!
//! ## Lean specification (`Pythia.Finance.Options.VolatilityTradingPnL`)
//!
//! - **Daily gamma PnL nonneg** when realized > implied (`daily_gamma_pnl_pos`)
//! - **Theta offsets gamma** (`theta_gamma_offset`)
//! - **Cumulative PnL nonneg** for positive daily PnLs (`cumulative_vol_pnl_nonneg`)
//! - **Vol arb breakeven**: profit iff realized > implied (`vol_arb_breakeven`)
//! - **Vega PnL nonneg** for long vega + vol rise (`vega_pnl_nonneg`)

/// Daily gamma PnL: (1/2)*Γ*S²*(σ_r² - σ_i²)*dt.
/// # Lean: `daily_gamma_pnl_pos`
pub fn daily_gamma_pnl(gamma: f64, spot_sq: f64, realized_var: f64, implied_var: f64, dt: f64) -> f64 {
    gamma / 2.0 * spot_sq * (realized_var - implied_var) * dt
}

/// Net daily PnL: gamma PnL + theta.
/// # Lean: `theta_gamma_offset`
pub fn net_daily_pnl(gamma_pnl: f64, theta: f64) -> f64 {
    gamma_pnl + theta
}

/// Cumulative vol PnL over multiple days.
/// # Lean: `cumulative_vol_pnl_nonneg`
pub fn cumulative_pnl(daily_pnls: &[f64]) -> f64 {
    daily_pnls.iter().sum()
}

/// Vol arb breakeven: realized - implied.
/// # Lean: `vol_arb_breakeven`
pub fn vol_arb_profit(realized_vol: f64, implied_vol: f64) -> f64 {
    realized_vol - implied_vol
}

/// Vega PnL: vega * Δiv.
/// # Lean: `vega_pnl_nonneg`
pub fn vega_pnl(vega: f64, dv: f64) -> f64 {
    vega * dv
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gamma_pnl_pos_when_realized_gt_implied() {
        assert!(daily_gamma_pnl(0.03, 10000.0, 0.05, 0.04, 1.0/252.0) > 0.0);
    }

    #[test]
    fn gamma_pnl_neg_when_realized_lt_implied() {
        assert!(daily_gamma_pnl(0.03, 10000.0, 0.03, 0.04, 1.0/252.0) < 0.0);
    }

    #[test]
    fn net_pnl_decomposition() {
        let g = 5.0;
        let t = -3.0;
        assert!((net_daily_pnl(g, t) - 2.0).abs() < 1e-10);
    }

    #[test]
    fn cumulative_nonneg_from_positive_days() {
        assert!(cumulative_pnl(&[1.0, 2.0, 0.5]) >= 0.0);
    }

    #[test]
    fn vol_arb_breakeven() {
        assert!(vol_arb_profit(0.25, 0.20) > 0.0);
        assert!(vol_arb_profit(0.20, 0.20) == 0.0);
    }

    #[test]
    fn vega_pnl_long_vol_rise() {
        assert!(vega_pnl(1000.0, 0.02) > 0.0);
    }
}
