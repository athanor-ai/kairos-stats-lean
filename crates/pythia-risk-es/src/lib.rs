//! # pythia-risk-es
//!
//! Verified Expected Shortfall (CVaR) for normal distributions.
//!
//! ## Lean specification (`Pythia.Finance.ExpectedShortfall`)
//!
//! - **ES = -μ + σh** (`esNormal`)
//! - **Zero-mean**: ES(0,σ) = σh (`esNormal_zero_mean`)
//! - **Positive homogeneity**: ES(αμ,ασ) = α·ES(μ,σ) (`esNormal_pos_homogeneous`)
//! - **Translation invariance**: ES(μ+c,σ) = ES(μ,σ) - c (`esNormal_translation`)
//! - **ES ≥ VaR** when h ≥ z (`esNormal_dominates_varNormal`)

/// Normal-distribution ES: -μ + σ*h where h = φ(z_α)/α.
/// # Lean: `esNormal`
#[inline(always)]
pub fn es_normal(mu: f64, sigma: f64, h: f64) -> f64 {
    -mu + sigma * h
}

/// Normal-distribution VaR: -μ + σ*z where z = Φ⁻¹(1-α).
pub fn var_normal(mu: f64, sigma: f64, z: f64) -> f64 {
    -mu + sigma * z
}

/// ES dominates VaR: ES - VaR = σ*(h-z) ≥ 0 when h ≥ z, σ ≥ 0.
/// # Lean: `esNormal_dominates_varNormal`
pub fn es_var_gap(sigma: f64, h: f64, z: f64) -> f64 {
    sigma * (h - z)
}

/// Check positive homogeneity: ES(αμ,ασ) = α·ES(μ,σ).
/// # Lean: `esNormal_pos_homogeneous`
pub fn check_pos_homogeneous(alpha: f64, mu: f64, sigma: f64, h: f64, tol: f64) -> bool {
    (es_normal(alpha * mu, alpha * sigma, h) - alpha * es_normal(mu, sigma, h)).abs() < tol
}

/// Check translation invariance: ES(μ+c,σ) = ES(μ,σ) - c.
/// # Lean: `esNormal_translation`
pub fn check_translation(mu: f64, sigma: f64, h: f64, c: f64, tol: f64) -> bool {
    (es_normal(mu + c, sigma, h) - (es_normal(mu, sigma, h) - c)).abs() < tol
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_mean() {
        assert!((es_normal(0.0, 0.2, 2.06) - 0.2 * 2.06).abs() < 1e-10);
    }

    #[test]
    fn es_ge_var() {
        let h = 2.06; let z = 1.645;
        let es = es_normal(0.0, 0.2, h);
        let var = var_normal(0.0, 0.2, z);
        assert!(es >= var);
    }

    #[test]
    fn pos_homogeneous() {
        assert!(check_pos_homogeneous(3.0, 0.05, 0.2, 2.06, 1e-10));
    }

    #[test]
    fn translation_invariant() {
        assert!(check_translation(0.05, 0.2, 2.06, 0.03, 1e-10));
    }

    #[test]
    fn gap_nonneg() {
        assert!(es_var_gap(0.2, 2.06, 1.645) >= 0.0);
    }
}
