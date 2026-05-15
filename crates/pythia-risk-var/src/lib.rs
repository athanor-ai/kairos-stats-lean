//! # pythia-risk-var
//!
//! Verified Value-at-Risk (normal closed form).
//!
//! ## Lean specification (`Pythia.Finance.ValueAtRisk`)
//!
//! - **VaR = -μ + σz** (`varNormal`)
//! - **Zero-mean**: VaR(0,σ) = σz (`varNormal_zero_mean`)
//! - **Positive homogeneity**: VaR(αμ,ασ) = α·VaR(μ,σ) (`varNormal_pos_homogeneous`)
//! - **Monotone in σ** for z ≥ 0 (`varNormal_mono_in_sigma`)
//! - **Translation invariance**: VaR(μ+c,σ) = VaR(μ,σ) - c (`varNormal_translation`)

/// Normal VaR: -μ + σ*z.
/// # Lean: `varNormal`
#[inline(always)]
pub fn var_normal(mu: f64, sigma: f64, z: f64) -> f64 {
    -mu + sigma * z
}

/// Common z-values for standard confidence levels.
pub const Z_95: f64 = 1.6449;
pub const Z_99: f64 = 2.3263;
pub const Z_997: f64 = 2.7478;

/// Check positive homogeneity.
/// # Lean: `varNormal_pos_homogeneous`
pub fn check_pos_homogeneous(alpha: f64, mu: f64, sigma: f64, z: f64, tol: f64) -> bool {
    (var_normal(alpha * mu, alpha * sigma, z) - alpha * var_normal(mu, sigma, z)).abs() < tol
}

/// Check translation invariance.
/// # Lean: `varNormal_translation`
pub fn check_translation(mu: f64, sigma: f64, z: f64, c: f64, tol: f64) -> bool {
    (var_normal(mu + c, sigma, z) - (var_normal(mu, sigma, z) - c)).abs() < tol
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_mean() {
        assert!((var_normal(0.0, 0.2, Z_99) - 0.2 * Z_99).abs() < 1e-10);
    }

    #[test]
    fn pos_homogeneous() {
        assert!(check_pos_homogeneous(3.0, 0.05, 0.2, Z_99, 1e-10));
    }

    #[test]
    fn translation() {
        assert!(check_translation(0.05, 0.2, Z_99, 0.03, 1e-10));
    }

    #[test]
    fn mono_sigma() {
        assert!(var_normal(0.0, 0.1, Z_99) <= var_normal(0.0, 0.3, Z_99));
    }

    #[test]
    fn higher_confidence_higher_var() {
        assert!(var_normal(0.0, 0.2, Z_95) <= var_normal(0.0, 0.2, Z_99));
    }
}
