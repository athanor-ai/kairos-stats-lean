//! # Mean-Variance Portfolio Optimality (convex objective)
//!
//! Rust port of `Pythia.Finance.Portfolio.PortfolioOptimality`.
//!
//! A two-asset portfolio has variance (the mean-variance objective):
//!
//! ```text
//! V(w) = w^2 * v1 + (1-w)^2 * v2 + 2*w*(1-w) * cov
//! ```
//!
//! This is a quadratic in w. Under the PSD condition `v1 + v2 > 2*cov`,
//! the second derivative is positive making the objective strictly convex
//! and admitting a unique minimizer via the first-order condition.
//!
//! ## Lean theorems mirrored
//!
//! - [`mv_objective`] — definition of portfolio variance
//! - [`mv_objective_second_deriv`] — 2*(v1 + v2 - 2*cov)
//! - [`optimal_weight`] — FOC minimizer (v2 - cov) / (v1 + v2 - 2*cov)
//! - [`portfolio_return`] — affine return w*mu1 + (1-w)*mu2
//! - [`diversification_benefit`] — equal-weight zero-cov variance <= avg variance

/// Mean-variance objective: portfolio variance as a function of weight `w`
/// on asset 1.
///
/// Corresponds to Lean `mvObjective`.
///
/// ```text
/// V(w) = w^2 * v1 + (1-w)^2 * v2 + 2*w*(1-w) * cov
/// ```
#[inline]
pub fn mv_objective(v1: f64, v2: f64, cov: f64, w: f64) -> f64 {
    w * w * v1 + (1.0 - w) * (1.0 - w) * v2 + 2.0 * w * (1.0 - w) * cov
}

/// Second derivative of the mean-variance objective w.r.t. w.
///
/// Corresponds to Lean `mvObjective_second_deriv_pos`: when
/// `v1 + v2 > 2*cov` this is strictly positive, confirming strict convexity.
///
/// ```text
/// d^2V/dw^2 = 2*(v1 + v2 - 2*cov)
/// ```
#[inline]
pub fn mv_objective_second_deriv(v1: f64, v2: f64, cov: f64) -> f64 {
    2.0 * (v1 + v2 - 2.0 * cov)
}

/// Returns true when the objective is strictly convex (second derivative > 0).
///
/// This is the PSD condition: `v1 + v2 > 2*cov`.
#[inline]
pub fn is_strictly_convex(v1: f64, v2: f64, cov: f64) -> bool {
    v1 + v2 > 2.0 * cov
}

/// Optimal weight on asset 1 (FOC minimizer).
///
/// Corresponds to Lean `optimalWeight`:
///
/// ```text
/// w* = (v2 - cov) / (v1 + v2 - 2*cov)
/// ```
///
/// Requires `v1 + v2 - 2*cov != 0` (the denominator is non-zero under PSD).
/// Returns `f64::NAN` if the denominator is zero.
#[inline]
pub fn optimal_weight(v1: f64, v2: f64, cov: f64) -> f64 {
    let denom = v1 + v2 - 2.0 * cov;
    if denom == 0.0 {
        f64::NAN
    } else {
        (v2 - cov) / denom
    }
}

/// Verify that the FOC (first-order condition) holds at the optimal weight.
///
/// The derivative dV/dw evaluated at w* should be zero (within tolerance).
/// dV/dw = 2*w*v1 - 2*(1-w)*v2 + 2*(1-2w)*cov
///
/// Corresponds to Lean `optimalWeight_foc`.
#[inline]
pub fn foc_residual(v1: f64, v2: f64, cov: f64) -> f64 {
    let w = optimal_weight(v1, v2, cov);
    2.0 * w * v1 - 2.0 * (1.0 - w) * v2 + 2.0 * (1.0 - 2.0 * w) * cov
}

/// Portfolio return as an affine function of weight.
///
/// Corresponds to Lean `portfolioReturn`:
///
/// ```text
/// R(w) = w * mu1 + (1-w) * mu2
/// ```
#[inline]
pub fn portfolio_return(mu1: f64, mu2: f64, w: f64) -> f64 {
    w * mu1 + (1.0 - w) * mu2
}

/// Diversification benefit check: at equal weight (w=1/2) with zero
/// covariance, portfolio variance <= average of individual variances.
///
/// Corresponds to Lean `diversification_benefit`:
///
/// ```text
/// V(1/2) = (v1 + v2) / 4 <= (v1 + v2) / 2
/// ```
///
/// Returns `true` when `V(1/2, cov=0) <= (v1 + v2) / 2`.
#[inline]
pub fn diversification_benefit(v1: f64, v2: f64) -> bool {
    let portfolio_var = mv_objective(v1, v2, 0.0, 0.5);
    let avg_var = (v1 + v2) / 2.0;
    portfolio_var <= avg_var
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Lean: `mvObjective_at_zero` — V(0) = v2
    #[test]
    fn test_objective_at_zero() {
        let v1 = 0.04;
        let v2 = 0.09;
        let cov = 0.01;
        let result = mv_objective(v1, v2, cov, 0.0);
        assert!((result - v2).abs() < EPS, "V(0) should equal v2");
    }

    /// Lean: `mvObjective_at_one` — V(1) = v1
    #[test]
    fn test_objective_at_one() {
        let v1 = 0.04;
        let v2 = 0.09;
        let cov = 0.01;
        let result = mv_objective(v1, v2, cov, 1.0);
        assert!((result - v1).abs() < EPS, "V(1) should equal v1");
    }

    /// Lean: `mvObjective_second_deriv_pos` — strict convexity under PSD
    #[test]
    fn test_second_deriv_positive() {
        let v1 = 0.04;
        let v2 = 0.09;
        let cov = 0.02; // v1 + v2 = 0.13 > 0.04 = 2*cov
        let d2 = mv_objective_second_deriv(v1, v2, cov);
        assert!(d2 > 0.0, "second derivative should be positive under PSD");
        assert!(is_strictly_convex(v1, v2, cov));
    }

    /// Lean: `optimalWeight_foc` — FOC residual is zero
    #[test]
    fn test_foc_zero() {
        let v1 = 0.04;
        let v2 = 0.09;
        let cov = 0.02;
        let residual = foc_residual(v1, v2, cov);
        assert!(residual.abs() < EPS, "FOC residual should be zero, got {}", residual);
    }

    /// Lean: `portfolioReturn_affine` — R(w) = mu2 + w*(mu1-mu2)
    #[test]
    fn test_return_affine() {
        let mu1 = 0.12;
        let mu2 = 0.06;
        let w = 0.4;
        let r = portfolio_return(mu1, mu2, w);
        let affine = mu2 + w * (mu1 - mu2);
        assert!((r - affine).abs() < EPS, "return should be affine in w");
    }

    /// Lean: `diversification_benefit` — equal-weight zero-cov reduces variance
    #[test]
    fn test_diversification_benefit() {
        assert!(diversification_benefit(0.04, 0.09));
        assert!(diversification_benefit(0.0, 0.0)); // degenerate: 0 <= 0
        assert!(diversification_benefit(1.0, 1.0)); // 0.5 <= 1.0
    }
}
