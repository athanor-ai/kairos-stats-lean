//! # pythia-portfolio-efficient-frontier
//!
//! Rust port of `Pythia.Finance.Portfolio.EfficientFrontier`.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.EfficientFrontier`)
//!
//! - **portfolioReturn**: `w * mu1 + (1 - w) * mu2`
//! - **portfolioVar**: `w^2 * v1 + (1-w)^2 * v2 + 2*w*(1-w)*cov`
//! - **portfolioReturn_at_zero**: weight 0 gives mu2
//! - **portfolioReturn_at_one**: weight 1 gives mu1
//! - **portfolioReturn_linear**: return is affine in w
//! - **portfolioVar_at_zero**: weight 0 gives v2
//! - **portfolioVar_at_one**: weight 1 gives v1
//! - **portfolioVar_nonneg_uncorrelated**: nonneg for zero cov + nonneg variances

/// Expected return of a two-asset portfolio with weight `w` on asset 1.
///
/// # Lean: `portfolioReturn`
#[inline]
pub fn portfolio_return(w: f64, mu1: f64, mu2: f64) -> f64 {
    w * mu1 + (1.0 - w) * mu2
}

/// Variance of a two-asset portfolio with weight `w` on asset 1.
///
/// # Lean: `portfolioVar`
#[inline]
pub fn portfolio_var(w: f64, v1: f64, v2: f64, cov: f64) -> f64 {
    w * w * v1 + (1.0 - w) * (1.0 - w) * v2 + 2.0 * w * (1.0 - w) * cov
}

/// Portfolio return expressed as affine interpolation:
/// `mu2 + w * (mu1 - mu2)`.
///
/// # Lean: `portfolioReturn_linear`
#[inline]
pub fn portfolio_return_linear(w: f64, mu1: f64, mu2: f64) -> f64 {
    mu2 + w * (mu1 - mu2)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Lean: `portfolioReturn_at_zero` — weight 0 gives pure asset-2 return
    #[test]
    fn test_return_at_zero() {
        let r = portfolio_return(0.0, 0.12, 0.08);
        assert!((r - 0.08).abs() < EPS);
    }

    /// Lean: `portfolioReturn_at_one` — weight 1 gives pure asset-1 return
    #[test]
    fn test_return_at_one() {
        let r = portfolio_return(1.0, 0.12, 0.08);
        assert!((r - 0.12).abs() < EPS);
    }

    /// Lean: `portfolioReturn_linear` — return is affine in w
    #[test]
    fn test_return_linear() {
        let w = 0.6;
        let mu1 = 0.15;
        let mu2 = 0.05;
        let r = portfolio_return(w, mu1, mu2);
        let r_lin = portfolio_return_linear(w, mu1, mu2);
        assert!((r - r_lin).abs() < EPS);
    }

    /// Lean: `portfolioVar_at_zero` — weight 0 gives pure asset-2 variance
    #[test]
    fn test_var_at_zero() {
        let v = portfolio_var(0.0, 0.04, 0.09, 0.01);
        assert!((v - 0.09).abs() < EPS);
    }

    /// Lean: `portfolioVar_at_one` — weight 1 gives pure asset-1 variance
    #[test]
    fn test_var_at_one() {
        let v = portfolio_var(1.0, 0.04, 0.09, 0.01);
        assert!((v - 0.04).abs() < EPS);
    }

    /// Lean: `portfolioVar_nonneg_uncorrelated` — nonneg when cov=0 and v1,v2>=0
    #[test]
    fn test_var_nonneg_uncorrelated() {
        for w in [0.0, 0.25, 0.5, 0.75, 1.0, -0.5, 1.5] {
            let v = portfolio_var(w, 0.04, 0.09, 0.0);
            assert!(v >= -EPS, "var should be nonneg at w={}, got {}", w, v);
        }
    }
}
