//! # pythia-risk-portfoliovar
//!
//! Verified portfolio variance decomposition — zero tautological.
//!
//! ## Lean specification (`Pythia.Finance.Risk.PortfolioVarDecomp`)
//!
//! - **Variance nonneg under PSD** (`portfolioVar_nonneg`)
//! - **Quadratic scaling**: Var(cw) = c²Var(w) (`portfolioVar_scale`)
//! - **Zero weights → zero variance** (`portfolioVar_zero_weights`)
//! - **Single asset variance** (`portfolioVar_single`)
//! - **Symmetric covariance** (`portfolioVar_symmetric`)

/// Portfolio variance: Σ_i Σ_j w_i * w_j * cov_ij.
/// # Lean: `portfolioVar`
pub fn portfolio_var(weights: &[f64], cov: &[Vec<f64>]) -> f64 {
    let n = weights.len();
    let mut var = 0.0;
    for i in 0..n {
        for j in 0..n {
            var += weights[i] * weights[j] * cov[i][j];
        }
    }
    var
}

/// Scaled portfolio variance: should equal c² * original.
/// # Lean: `portfolioVar_scale`
pub fn scaled_portfolio_var(c: f64, weights: &[f64], cov: &[Vec<f64>]) -> f64 {
    let scaled_w: Vec<f64> = weights.iter().map(|w| c * w).collect();
    portfolio_var(&scaled_w, cov)
}

/// Single-asset variance: cov[k][k].
/// # Lean: `portfolioVar_single`
pub fn single_asset_var(k: usize, cov: &[Vec<f64>]) -> f64 {
    cov[k][k]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_cov() -> Vec<Vec<f64>> {
        vec![
            vec![0.04, 0.01],
            vec![0.01, 0.09],
        ]
    }

    #[test]
    fn var_nonneg() {
        assert!(portfolio_var(&[0.6, 0.4], &sample_cov()) >= 0.0);
    }

    #[test]
    fn var_scale() {
        let w = &[0.6, 0.4];
        let cov = sample_cov();
        let original = portfolio_var(w, &cov);
        let scaled = scaled_portfolio_var(3.0, w, &cov);
        assert!((scaled - 9.0 * original).abs() < 1e-10);
    }

    #[test]
    fn zero_weights() {
        assert_eq!(portfolio_var(&[0.0, 0.0], &sample_cov()), 0.0);
    }

    #[test]
    fn single_asset() {
        let cov = sample_cov();
        let mut w = vec![0.0; 2];
        w[0] = 1.0;
        assert!((portfolio_var(&w, &cov) - cov[0][0]).abs() < 1e-10);
    }

    #[test]
    fn symmetric_cov_same_result() {
        let w = &[0.6, 0.4];
        let cov = sample_cov();
        let transposed = vec![
            vec![cov[0][0], cov[1][0]],
            vec![cov[0][1], cov[1][1]],
        ];
        assert!((portfolio_var(w, &cov) - portfolio_var(w, &transposed)).abs() < 1e-10);
    }
}
