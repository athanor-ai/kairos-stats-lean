//! Mean-variance portfolio optimality.
//!
//! Lean spec: `Pythia.Finance.PortfolioOptimality`
//!
//! Theorems modelled:
//! - `mvObjective`: w^2*v1 + (1-w)^2*v2 + 2*w*(1-w)*cov
//! - `mvObjective_second_deriv_pos`: strictly convex when cov < (v1+v2)/2
//! - `optimalWeight`: (v2 - cov) / (v1 + v2 - 2*cov)
//! - `optimalWeight_foc`: FOC = 0 at optimal weight
//! - `portfolioReturn_affine`: return is affine in weight
//! - `diversification_benefit`: equal-weight variance <= average individual variances

/// Two-asset mean-variance optimizer.
#[derive(Debug, Clone, Copy)]
pub struct MeanVarianceOptimizer {
    /// Variance of asset 1.
    pub v1: f64,
    /// Variance of asset 2.
    pub v2: f64,
    /// Covariance between asset 1 and asset 2.
    pub cov: f64,
    /// Expected return of asset 1.
    pub r1: f64,
    /// Expected return of asset 2.
    pub r2: f64,
}

impl MeanVarianceOptimizer {
    pub fn new(v1: f64, v2: f64, cov: f64, r1: f64, r2: f64) -> Self {
        Self { v1, v2, cov, r1, r2 }
    }

    /// Portfolio variance as a function of weight w in asset 1.
    ///
    /// Lean: `mvObjective`
    /// sigma_p^2 = w^2*v1 + (1-w)^2*v2 + 2*w*(1-w)*cov
    pub fn mv_objective(&self, w: f64) -> f64 {
        w * w * self.v1 + (1.0 - w) * (1.0 - w) * self.v2 + 2.0 * w * (1.0 - w) * self.cov
    }

    /// Second derivative of mv_objective w.r.t. w.
    ///
    /// Lean: `mvObjective_second_deriv_pos`
    /// d^2/dw^2 = 2*(v1 + v2 - 2*cov), positive when cov < (v1+v2)/2.
    pub fn second_deriv(&self) -> f64 {
        2.0 * (self.v1 + self.v2 - 2.0 * self.cov)
    }

    /// Whether the objective is strictly convex (has a unique minimum).
    pub fn is_strictly_convex(&self) -> bool {
        self.second_deriv() > 0.0
    }

    /// Optimal weight in asset 1 that minimizes portfolio variance.
    ///
    /// Lean: `optimalWeight`
    /// w* = (v2 - cov) / (v1 + v2 - 2*cov)
    ///
    /// Returns `None` if the denominator is zero (degenerate case).
    pub fn optimal_weight(&self) -> Option<f64> {
        let denom = self.v1 + self.v2 - 2.0 * self.cov;
        if denom.abs() < 1e-15 {
            return None;
        }
        Some((self.v2 - self.cov) / denom)
    }

    /// First-order condition evaluated at weight w.
    ///
    /// Lean: `optimalWeight_foc`
    /// FOC: d/dw [mv_objective] = 2*w*v1 - 2*(1-w)*v2 + 2*(1-2w)*cov = 0
    pub fn foc(&self, w: f64) -> f64 {
        2.0 * w * self.v1 - 2.0 * (1.0 - w) * self.v2 + 2.0 * (1.0 - 2.0 * w) * self.cov
    }

    /// Portfolio expected return as an affine function of weight.
    ///
    /// Lean: `portfolioReturn_affine`
    /// E[r_p] = w * r1 + (1 - w) * r2
    pub fn portfolio_return(&self, w: f64) -> f64 {
        w * self.r1 + (1.0 - w) * self.r2
    }

    /// Check diversification benefit for equal-weight portfolio.
    ///
    /// Lean: `diversification_benefit`
    /// Var(0.5*X + 0.5*Y) = (v1 + v2 + 2*cov)/4 <= (v1 + v2)/2
    /// This holds whenever cov <= (v1 + v2)/2, which is guaranteed by
    /// Cauchy-Schwarz (cov <= sqrt(v1*v2) <= (v1+v2)/2).
    pub fn diversification_benefit(&self) -> bool {
        let equal_weight_var = self.mv_objective(0.5);
        let avg_var = (self.v1 + self.v2) / 2.0;
        equal_weight_var <= avg_var + 1e-15
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_opt() -> MeanVarianceOptimizer {
        // v1=0.04, v2=0.09, cov=0.01, r1=0.08, r2=0.12
        MeanVarianceOptimizer::new(0.04, 0.09, 0.01, 0.08, 0.12)
    }

    #[test]
    fn test_mv_objective_at_extremes() {
        let o = sample_opt();
        assert!((o.mv_objective(1.0) - o.v1).abs() < 1e-12);
        assert!((o.mv_objective(0.0) - o.v2).abs() < 1e-12);
    }

    #[test]
    fn test_second_deriv_positive() {
        // Lean: mvObjective_second_deriv_pos
        let o = sample_opt();
        assert!(o.is_strictly_convex());
        assert!(o.second_deriv() > 0.0);
    }

    #[test]
    fn test_optimal_weight_value() {
        // Lean: optimalWeight
        let o = sample_opt();
        let w = o.optimal_weight().unwrap();
        let expected = (0.09 - 0.01) / (0.04 + 0.09 - 0.02);
        assert!((w - expected).abs() < 1e-12);
    }

    #[test]
    fn test_foc_at_optimum() {
        // Lean: optimalWeight_foc — FOC = 0 at w*
        let o = sample_opt();
        let w = o.optimal_weight().unwrap();
        assert!(o.foc(w).abs() < 1e-10);
    }

    #[test]
    fn test_portfolio_return_affine() {
        // Lean: portfolioReturn_affine
        let o = sample_opt();
        assert!((o.portfolio_return(1.0) - o.r1).abs() < 1e-12);
        assert!((o.portfolio_return(0.0) - o.r2).abs() < 1e-12);
        // midpoint
        let mid = o.portfolio_return(0.5);
        assert!((mid - 0.5 * (o.r1 + o.r2)).abs() < 1e-12);
    }

    #[test]
    fn test_diversification_benefit() {
        // Lean: diversification_benefit
        let o = sample_opt();
        assert!(o.diversification_benefit());
    }

    #[test]
    fn test_optimal_minimizes() {
        let o = sample_opt();
        let w_star = o.optimal_weight().unwrap();
        let var_star = o.mv_objective(w_star);
        // Check nearby weights are worse
        for &dw in &[-0.1, -0.01, 0.01, 0.1] {
            assert!(o.mv_objective(w_star + dw) >= var_star - 1e-12);
        }
    }

    #[test]
    fn test_degenerate_returns_none() {
        // When v1 = v2 = cov, denominator is zero
        let o = MeanVarianceOptimizer::new(0.04, 0.04, 0.04, 0.1, 0.1);
        assert!(o.optimal_weight().is_none());
    }
}
