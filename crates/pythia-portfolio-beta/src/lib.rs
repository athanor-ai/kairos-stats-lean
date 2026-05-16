//! # pythia-portfolio-beta
//!
//! Verified CAPM beta via correlation identity.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.BetaFromCorrelation`)
//!
//! - **Beta from correlation**: `beta = rho * sigma_p / sigma_m`
//! - **Zero correlation**: `rho = 0` implies `beta = 0`
//! - **Unit correlation**: `rho = 1` implies `beta = sigma_p / sigma_m`
//! - **Scale in portfolio vol**: scaling `sigma_p` by `alpha` scales beta by `alpha`

/// CAPM beta via correlation: `beta = rho * sigma_p / sigma_m`.
///
/// # Lean: `betaFromCorrelation`
#[inline(always)]
pub fn beta_from_correlation(rho: f64, sigma_p: f64, sigma_m: f64) -> f64 {
    rho * sigma_p / sigma_m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_correlation_gives_zero_beta() {
        assert_eq!(beta_from_correlation(0.0, 0.2, 0.15), 0.0);
    }

    #[test]
    fn unit_correlation_gives_vol_ratio() {
        let sigma_p = 0.25;
        let sigma_m = 0.15;
        let beta = beta_from_correlation(1.0, sigma_p, sigma_m);
        assert!((beta - sigma_p / sigma_m).abs() < 1e-15);
    }

    #[test]
    fn negative_correlation_gives_negative_beta() {
        let beta = beta_from_correlation(-0.5, 0.2, 0.15);
        assert!(beta < 0.0);
    }

    #[test]
    fn scale_portfolio_vol() {
        let rho = 0.7;
        let sigma_p = 0.2;
        let sigma_m = 0.15;
        let alpha = 2.0;
        let beta_base = beta_from_correlation(rho, sigma_p, sigma_m);
        let beta_scaled = beta_from_correlation(rho, alpha * sigma_p, sigma_m);
        assert!((beta_scaled - alpha * beta_base).abs() < 1e-12);
    }

    #[test]
    fn market_beta_is_one_when_equal_vol() {
        // rho=1, sigma_p = sigma_m => beta = 1
        let beta = beta_from_correlation(1.0, 0.15, 0.15);
        assert!((beta - 1.0).abs() < 1e-15);
    }

    #[test]
    fn beta_proportional_to_rho() {
        let sigma_p = 0.2;
        let sigma_m = 0.15;
        let b1 = beta_from_correlation(0.3, sigma_p, sigma_m);
        let b2 = beta_from_correlation(0.6, sigma_p, sigma_m);
        assert!((b2 - 2.0 * b1).abs() < 1e-12);
    }
}
