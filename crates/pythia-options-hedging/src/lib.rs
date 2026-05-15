//! Delta hedging decomposition.
//!
//! Lean spec: `Pythia.Finance.DeltaHedging`
//!
//! Theorems modelled:
//! - `hedgeError`: dC - delta * dS
//! - `hedgePnL_from_decomposition`: hedge error = theta*dt + gamma PnL
//! - `gammaPnL_nonneg`: long gamma always profits from moves (gamma/2 * dS^2)
//! - `gammaPnL_symmetric`: gamma PnL same for up/down moves
//! - `vol_arb_profit`: realized > implied => long gamma profits
//! - `perfect_hedge`: theta + gamma_pnl = 0 => zero hedge error

/// Parameters for a delta-hedged option position.
#[derive(Debug, Clone, Copy)]
pub struct DeltaHedge {
    /// Option delta (dC/dS).
    pub delta: f64,
    /// Option gamma (d^2C/dS^2).
    pub gamma: f64,
    /// Option theta (dC/dt), typically negative for long options.
    pub theta: f64,
}

impl DeltaHedge {
    /// Create a new delta hedge specification.
    pub fn new(delta: f64, gamma: f64, theta: f64) -> Self {
        Self { delta, gamma, theta }
    }

    /// Hedge error: change in option value minus delta-hedge P&L.
    ///
    /// Lean: `hedgeError`
    /// hedgeError = dC - delta * dS
    pub fn hedge_error(&self, dc: f64, ds: f64) -> f64 {
        dc - self.delta * ds
    }

    /// Gamma P&L component: 0.5 * gamma * dS^2.
    ///
    /// Lean: `gammaPnL_nonneg` — this quantity is non-negative when gamma >= 0.
    /// Lean: `gammaPnL_symmetric` — depends only on dS^2, so symmetric in sign of dS.
    pub fn gamma_pnl(&self, ds: f64) -> f64 {
        0.5 * self.gamma * ds * ds
    }

    /// Decompose hedge P&L into theta and gamma components.
    ///
    /// Lean: `hedgePnL_from_decomposition`
    /// hedge_error ≈ theta * dt + 0.5 * gamma * dS^2
    pub fn hedge_pnl_decomposition(&self, dt: f64, ds: f64) -> f64 {
        self.theta * dt + self.gamma_pnl(ds)
    }

    /// Check whether the hedge is perfect: theta + gamma_pnl = 0 within tolerance.
    ///
    /// Lean: `perfect_hedge`
    /// When theta * dt + gamma_pnl = 0, the hedge error is zero.
    pub fn is_perfect_hedge(&self, dt: f64, ds: f64, tol: f64) -> bool {
        self.hedge_pnl_decomposition(dt, ds).abs() < tol
    }
}

/// Volatility arbitrage P&L for a delta-hedged position.
///
/// Lean: `vol_arb_profit`
/// When realized_vol > implied_vol and gamma > 0, the position profits.
///
/// Returns the annualized P&L per unit gamma:
///   0.5 * gamma * S^2 * (realized_vol^2 - implied_vol^2) * dt
pub fn vol_arb_pnl(gamma: f64, spot: f64, realized_vol: f64, implied_vol: f64, dt: f64) -> f64 {
    0.5 * gamma * spot * spot * (realized_vol * realized_vol - implied_vol * implied_vol) * dt
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hedge_error_basic() {
        let h = DeltaHedge::new(0.5, 0.1, -0.05);
        // dC = 1.0, dS = 2.0 => hedge_error = 1.0 - 0.5*2.0 = 0.0
        assert!((h.hedge_error(1.0, 2.0)).abs() < 1e-12);
    }

    #[test]
    fn test_gamma_pnl_nonneg() {
        let h = DeltaHedge::new(0.5, 0.08, -0.03);
        assert!(h.gamma_pnl(1.5) >= 0.0);
        assert!(h.gamma_pnl(-1.5) >= 0.0);
        assert!(h.gamma_pnl(0.0).abs() < 1e-15);
    }

    #[test]
    fn test_gamma_pnl_symmetric() {
        let h = DeltaHedge::new(0.5, 0.12, -0.04);
        let up = h.gamma_pnl(2.0);
        let down = h.gamma_pnl(-2.0);
        assert!((up - down).abs() < 1e-12);
    }

    #[test]
    fn test_hedge_pnl_decomposition() {
        let h = DeltaHedge::new(0.5, 0.1, -0.02);
        let dt = 1.0 / 252.0;
        let ds = 1.0;
        let expected = h.theta * dt + 0.5 * h.gamma * ds * ds;
        assert!((h.hedge_pnl_decomposition(dt, ds) - expected).abs() < 1e-12);
    }

    #[test]
    fn test_vol_arb_profit_positive() {
        // realized > implied with long gamma => profit
        let pnl = vol_arb_pnl(0.05, 100.0, 0.30, 0.20, 1.0 / 252.0);
        assert!(pnl > 0.0);
    }

    #[test]
    fn test_vol_arb_loss_when_realized_lower() {
        // realized < implied with long gamma => loss
        let pnl = vol_arb_pnl(0.05, 100.0, 0.15, 0.25, 1.0 / 252.0);
        assert!(pnl < 0.0);
    }

    #[test]
    fn test_perfect_hedge() {
        // Construct theta and gamma so that theta*dt + gamma_pnl = 0
        let gamma = 0.1;
        let dt = 1.0 / 252.0;
        let ds = 1.0;
        let gamma_pnl = 0.5 * gamma * ds * ds;
        let theta = -gamma_pnl / dt;
        let h = DeltaHedge::new(0.5, gamma, theta);
        assert!(h.is_perfect_hedge(dt, ds, 1e-10));
    }
}
