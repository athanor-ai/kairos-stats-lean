//! # pythia-portfolio-efficient
//!
//! Verified two-asset efficient frontier (Markowitz, 1952).
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.EfficientFrontier`)
//!
//! - **portfolioReturn**: w*mu1 + (1-w)*mu2 (`portfolioReturn`)
//! - **portfolioVar**: w^2*v1 + (1-w)^2*v2 + 2*w*(1-w)*cov (`portfolioVar`)
//! - **At zero**: weight 0 gives pure asset-2 (`portfolioReturn_at_zero`, `portfolioVar_at_zero`)
//! - **At one**: weight 1 gives pure asset-1 (`portfolioReturn_at_one`, `portfolioVar_at_one`)
//! - **Linear**: return is affine in w (`portfolioReturn_linear`)
//! - **Nonneg uncorrelated**: var >= 0 when cov=0, v1>=0, v2>=0 (`portfolioVar_nonneg_uncorrelated`)

/// Expected return of a two-asset portfolio.
/// # Lean: `portfolioReturn`
#[inline(always)]
pub fn portfolio_return(w: f64, mu1: f64, mu2: f64) -> f64 {
    w * mu1 + (1.0 - w) * mu2
}

/// Variance of a two-asset portfolio (covariance-parametrised).
/// # Lean: `portfolioVar`
#[inline(always)]
pub fn portfolio_var(w: f64, v1: f64, v2: f64, cov: f64) -> f64 {
    w * w * v1 + (1.0 - w) * (1.0 - w) * v2 + 2.0 * w * (1.0 - w) * cov
}

/// Check affine interpolation property: return = mu2 + w*(mu1 - mu2).
/// # Lean: `portfolioReturn_linear`
pub fn check_return_linear(w: f64, mu1: f64, mu2: f64, tol: f64) -> bool {
    (portfolio_return(w, mu1, mu2) - (mu2 + w * (mu1 - mu2))).abs() < tol
}

/// Check non-negativity of variance under zero covariance.
/// # Lean: `portfolioVar_nonneg_uncorrelated`
pub fn check_var_nonneg_uncorrelated(w: f64, v1: f64, v2: f64) -> bool {
    v1 >= 0.0 && v2 >= 0.0 && portfolio_var(w, v1, v2, 0.0) >= -1e-15
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn return_at_zero() {
        // w=0 gives mu2
        assert!((portfolio_return(0.0, 0.10, 0.05) - 0.05).abs() < 1e-12);
    }

    #[test]
    fn return_at_one() {
        // w=1 gives mu1
        assert!((portfolio_return(1.0, 0.10, 0.05) - 0.10).abs() < 1e-12);
    }

    #[test]
    fn var_at_zero() {
        // w=0 gives v2
        assert!((portfolio_var(0.0, 0.04, 0.09, 0.01) - 0.09).abs() < 1e-12);
    }

    #[test]
    fn var_at_one() {
        // w=1 gives v1
        assert!((portfolio_var(1.0, 0.04, 0.09, 0.01) - 0.04).abs() < 1e-12);
    }

    #[test]
    fn return_linear() {
        assert!(check_return_linear(0.6, 0.12, 0.04, 1e-12));
    }

    #[test]
    fn var_nonneg_uncorrelated() {
        assert!(check_var_nonneg_uncorrelated(0.3, 0.04, 0.09));
        assert!(check_var_nonneg_uncorrelated(0.7, 0.01, 0.16));
    }
}
