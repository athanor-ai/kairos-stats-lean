//! Portfolio construction constraints.
//!
//! Lean spec: `Pythia.Finance.Portfolio.PortfolioConstruction`
//!
//! Theorems modelled:
//! - `weights_sum_one`: fully invested portfolio (weights sum to 1)
//! - `long_only`: all weights nonneg
//! - `max_position`: no single weight exceeds a limit
//! - `turnover`: sum of absolute weight changes
//! - `turnover_nonneg`: turnover is nonneg
//! - `zero_turnover_iff_unchanged`: zero turnover iff weights unchanged
//! - `rebalancing_cost_nonneg`: cost_rate * turnover >= 0
//! - `turnover_le_two`: for long-only portfolios summing to 1, turnover <= 2

/// A portfolio defined by asset weights.
#[derive(Debug, Clone)]
pub struct Portfolio {
    /// Weight of each asset. Must sum to 1 for a fully invested portfolio.
    pub weights: Vec<f64>,
}

impl Portfolio {
    pub fn new(weights: Vec<f64>) -> Self {
        Self { weights }
    }

    /// Number of assets.
    pub fn n(&self) -> usize {
        self.weights.len()
    }

    /// Sum of all weights.
    ///
    /// Lean: `weights_sum_one` -- a fully invested portfolio has sum = 1.
    pub fn weight_sum(&self) -> f64 {
        self.weights.iter().sum()
    }

    /// Whether the portfolio is fully invested (weights sum to 1).
    pub fn is_fully_invested(&self, tol: f64) -> bool {
        (self.weight_sum() - 1.0).abs() < tol
    }

    /// Whether the portfolio satisfies the long-only constraint.
    ///
    /// Lean: `long_only`
    pub fn is_long_only(&self) -> bool {
        self.weights.iter().all(|&w| w >= 0.0)
    }

    /// Whether every weight is at most `limit`.
    ///
    /// Lean: `max_position`
    pub fn satisfies_max_position(&self, limit: f64) -> bool {
        self.weights.iter().all(|&w| w <= limit + 1e-15)
    }
}

/// Turnover between two portfolios: sum of absolute weight changes.
///
/// Lean: `turnover`
pub fn turnover(old: &Portfolio, new: &Portfolio) -> f64 {
    assert_eq!(old.n(), new.n(), "portfolios must have same number of assets");
    old.weights
        .iter()
        .zip(new.weights.iter())
        .map(|(wo, wn)| (wn - wo).abs())
        .sum()
}

/// Rebalancing cost = cost_rate * turnover.
///
/// Lean: `rebalancing_cost_nonneg` -- nonneg when cost_rate >= 0.
pub fn rebalancing_cost(cost_rate: f64, old: &Portfolio, new: &Portfolio) -> f64 {
    cost_rate * turnover(old, new)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_portfolio() -> Portfolio {
        Portfolio::new(vec![0.3, 0.2, 0.15, 0.15, 0.2])
    }

    /// Lean: `weights_sum_one`
    #[test]
    fn test_weights_sum_one() {
        let p = sample_portfolio();
        assert!(p.is_fully_invested(1e-12));
    }

    /// Lean: `long_only`
    #[test]
    fn test_long_only() {
        let p = sample_portfolio();
        assert!(p.is_long_only());
        let short = Portfolio::new(vec![1.2, -0.2]);
        assert!(!short.is_long_only());
    }

    /// Lean: `max_position`
    #[test]
    fn test_max_position() {
        let p = sample_portfolio();
        assert!(p.satisfies_max_position(0.3));
        assert!(!p.satisfies_max_position(0.25));
    }

    /// Lean: `turnover_nonneg`
    #[test]
    fn test_turnover_nonneg() {
        let old = sample_portfolio();
        let new = Portfolio::new(vec![0.2, 0.3, 0.15, 0.15, 0.2]);
        assert!(turnover(&old, &new) >= 0.0);
    }

    /// Lean: `zero_turnover_iff_unchanged`
    #[test]
    fn test_zero_turnover_unchanged() {
        let p = sample_portfolio();
        let same = p.clone();
        assert!((turnover(&p, &same)).abs() < 1e-15);
    }

    /// Lean: `rebalancing_cost_nonneg`
    #[test]
    fn test_rebalancing_cost_nonneg() {
        let old = sample_portfolio();
        let new = Portfolio::new(vec![0.25, 0.25, 0.15, 0.15, 0.2]);
        let cost = rebalancing_cost(0.001, &old, &new);
        assert!(cost >= 0.0);
    }

    /// Lean: `turnover_le_two` -- for long-only, fully invested portfolios,
    /// turnover is at most 2.
    #[test]
    fn test_turnover_le_two_extreme() {
        // Sell everything in asset 0, buy everything in asset 1
        let old = Portfolio::new(vec![1.0, 0.0]);
        let new = Portfolio::new(vec![0.0, 1.0]);
        let t = turnover(&old, &new);
        assert!((t - 2.0).abs() < 1e-12);
        assert!(t <= 2.0 + 1e-12);
    }
}
