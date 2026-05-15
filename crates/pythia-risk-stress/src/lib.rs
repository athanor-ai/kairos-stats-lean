//! Stress testing properties for risk management.
//!
//! Lean spec: `Pythia.Finance.Risk.StressTest`
//!
//! Theorems modelled:
//! - `worst_case_bounded`: total loss <= n * max single-position loss
//! - `scenario_pnl_additive`: portfolio PnL = sum of per-position PnLs
//! - `diversification_in_stress`: |sum(pnls)| <= sum(|pnls|) (triangle inequality)
//! - `reverse_stress_breach`: sensitivity * magnitude > threshold means breach
//! - `long_portfolio_down_loss`: positive position * positive drop > 0
//! - `capital_adequate`: capital >= worst_loss implies survival (nonneg surplus)

/// Per-position losses under a stress scenario.
#[derive(Debug, Clone)]
pub struct StressScenario {
    /// PnL for each position (negative = loss).
    pub pnls: Vec<f64>,
}

impl StressScenario {
    pub fn new(pnls: Vec<f64>) -> Self {
        Self { pnls }
    }

    /// Number of positions.
    pub fn n(&self) -> usize {
        self.pnls.len()
    }

    /// Total portfolio PnL under this scenario.
    ///
    /// Lean: `scenario_pnl_additive`
    pub fn total_pnl(&self) -> f64 {
        self.pnls.iter().sum()
    }

    /// Sum of absolute PnLs (worst-case undiversified loss).
    pub fn sum_abs_pnl(&self) -> f64 {
        self.pnls.iter().map(|x| x.abs()).sum()
    }

    /// Worst-case bound: total loss <= n * max_loss.
    ///
    /// Lean: `worst_case_bounded`
    /// If every position loss <= max_loss, then sum(losses) <= n * max_loss.
    pub fn worst_case_bound(&self, max_loss: f64) -> f64 {
        self.n() as f64 * max_loss
    }

    /// Check that the worst-case bound holds.
    ///
    /// Lean: `worst_case_bounded`
    pub fn check_worst_case_bounded(&self, max_loss: f64) -> bool {
        if !self.pnls.iter().all(|&l| l <= max_loss + 1e-15) {
            return false;
        }
        self.total_pnl() <= self.worst_case_bound(max_loss) + 1e-12
    }

    /// Check triangle inequality (diversification in stress).
    ///
    /// Lean: `diversification_in_stress`
    /// |sum(pnls)| <= sum(|pnls|)
    pub fn check_diversification(&self) -> bool {
        self.total_pnl().abs() <= self.sum_abs_pnl() + 1e-12
    }
}

/// Reverse stress test: does sensitivity * magnitude breach the threshold?
///
/// Lean: `reverse_stress_breach`
pub fn reverse_stress_breaches(sensitivity: f64, magnitude: f64, threshold: f64) -> bool {
    sensitivity * magnitude > threshold
}

/// Loss on a long position in a down scenario.
///
/// Lean: `long_portfolio_down_loss`
/// position > 0 and price_drop > 0 implies loss > 0.
pub fn long_down_loss(position: f64, price_drop: f64) -> f64 {
    position * price_drop
}

/// Capital adequacy: surplus after absorbing worst-case loss.
///
/// Lean: `capital_adequate`
/// capital >= worst_loss implies surplus >= 0.
pub fn capital_surplus(capital: f64, worst_loss: f64) -> f64 {
    capital - worst_loss
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_scenario() -> StressScenario {
        StressScenario::new(vec![-100.0, -50.0, 20.0, -80.0, 10.0])
    }

    /// Lean: `worst_case_bounded`
    #[test]
    fn test_worst_case_bounded() {
        let s = StressScenario::new(vec![3.0, 5.0, 2.0, 4.0]);
        assert!(s.check_worst_case_bounded(5.0));
        // total = 14, bound = 4 * 5 = 20
        assert!(s.total_pnl() <= s.worst_case_bound(5.0));
    }

    /// Lean: `scenario_pnl_additive`
    #[test]
    fn test_scenario_pnl_additive() {
        let s = sample_scenario();
        let manual: f64 = vec![-100.0, -50.0, 20.0, -80.0, 10.0].iter().sum();
        assert!((s.total_pnl() - manual).abs() < 1e-12);
    }

    /// Lean: `diversification_in_stress`
    #[test]
    fn test_diversification_triangle() {
        let s = sample_scenario();
        assert!(s.check_diversification());
        // |sum| = |-200| = 200, sum(|x|) = 100+50+20+80+10 = 260
        assert!(s.total_pnl().abs() <= s.sum_abs_pnl() + 1e-12);
    }

    /// Lean: `reverse_stress_breach`
    #[test]
    fn test_reverse_stress_breach() {
        assert!(reverse_stress_breaches(2.0, 5.0, 9.0));  // 10 > 9
        assert!(!reverse_stress_breaches(2.0, 5.0, 10.0)); // 10 == 10, not >
        assert!(!reverse_stress_breaches(2.0, 5.0, 11.0)); // 10 < 11
    }

    /// Lean: `long_portfolio_down_loss`
    #[test]
    fn test_long_down_loss_positive() {
        let loss = long_down_loss(100.0, 0.05);
        assert!(loss > 0.0);
        assert!((loss - 5.0).abs() < 1e-12);
    }

    /// Lean: `capital_adequate`
    #[test]
    fn test_capital_adequate() {
        assert!(capital_surplus(1000.0, 800.0) >= 0.0);
        assert!(capital_surplus(800.0, 800.0) >= 0.0);
        assert!(capital_surplus(700.0, 800.0) < 0.0);
    }

    /// Extra: empty scenario has zero PnL.
    #[test]
    fn test_empty_scenario() {
        let s = StressScenario::new(vec![]);
        assert!((s.total_pnl()).abs() < 1e-15);
        assert!(s.check_diversification());
    }
}
