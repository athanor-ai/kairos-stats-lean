//! # pythia-portfolio-markowitz
//!
//! Rust port of `Pythia.Finance.Portfolio.MarkowitzFrontier`.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.MarkowitzFrontier`)
//!
//! - **minVarWeight1**: `(vY - cXY) / (vX + vY - 2*cXY)`
//! - **minVarVariance**: `(vX*vY - cXY^2) / (vX + vY - 2*cXY)`
//! - **minVarWeight1_zero_corr**: at cXY=0, weight = vY/(vX+vY) (inverse-variance)
//! - **minVarVariance_nonneg**: nonneg under PSD + positive denominator

/// Minimum-variance weight on asset 1 in a two-asset portfolio.
///
/// `w* = (vY - cXY) / (vX + vY - 2*cXY)`
///
/// # Lean: `minVarWeight1`
#[inline]
pub fn min_var_weight1(v_x: f64, v_y: f64, c_xy: f64) -> f64 {
    (v_y - c_xy) / (v_x + v_y - 2.0 * c_xy)
}

/// Minimum variance achievable in a two-asset portfolio.
///
/// `vS* = (vX*vY - cXY^2) / (vX + vY - 2*cXY)`
///
/// # Lean: `minVarVariance`
#[inline]
pub fn min_var_variance(v_x: f64, v_y: f64, c_xy: f64) -> f64 {
    (v_x * v_y - c_xy * c_xy) / (v_x + v_y - 2.0 * c_xy)
}

/// At zero correlation, the min-var weight equals the inverse-variance weight.
///
/// `minVarWeight1(vX, vY, 0) = vY / (vX + vY)`
///
/// # Lean: `minVarWeight1_zero_corr`
#[inline]
pub fn min_var_weight1_zero_corr(v_x: f64, v_y: f64) -> f64 {
    v_y / (v_x + v_y)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Lean: `minVarWeight1_zero_corr` — at cXY=0, weight = vY/(vX+vY)
    #[test]
    fn test_zero_corr_weight() {
        let v_x = 0.04;
        let v_y = 0.09;
        let w = min_var_weight1(v_x, v_y, 0.0);
        let expected = v_y / (v_x + v_y);
        assert!((w - expected).abs() < EPS);
    }

    /// Verify zero_corr helper matches general formula at cXY=0
    #[test]
    fn test_zero_corr_helper_matches() {
        let v_x = 0.16;
        let v_y = 0.25;
        let w_general = min_var_weight1(v_x, v_y, 0.0);
        let w_special = min_var_weight1_zero_corr(v_x, v_y);
        assert!((w_general - w_special).abs() < EPS);
    }

    /// Lean: `minVarVariance_nonneg` — nonneg under PSD condition
    #[test]
    fn test_min_var_nonneg() {
        let v_x = 0.04;
        let v_y = 0.09;
        let c_xy = 0.02; // cXY^2 = 0.0004 <= vX*vY = 0.0036
        let mv = min_var_variance(v_x, v_y, c_xy);
        assert!(mv >= -EPS, "min var should be nonneg, got {}", mv);
    }

    /// Equal variances + zero covariance => equal weights
    #[test]
    fn test_equal_var_equal_weight() {
        let v = 0.10;
        let w = min_var_weight1(v, v, 0.0);
        assert!((w - 0.5).abs() < EPS);
    }

    /// Negative covariance gives diversification benefit
    #[test]
    fn test_negative_cov_diversification() {
        let v_x = 0.04;
        let v_y = 0.04;
        let c_neg = -0.02;
        let mv = min_var_variance(v_x, v_y, c_neg);
        // With negative cov, min variance should be less than either individual
        assert!(mv < v_x);
        assert!(mv < v_y);
    }

    /// Perfect positive correlation => no diversification
    #[test]
    fn test_perfect_pos_corr() {
        let v_x = 0.04;
        let v_y = 0.09;
        // Perfect positive correlation: cXY = sqrt(vX)*sqrt(vY)
        let c_xy = (v_x * v_y).sqrt();
        let mv = min_var_variance(v_x, v_y, c_xy);
        // Should be approximately zero (perfect hedge)
        assert!(mv.abs() < EPS, "perfect corr min var should be ~0, got {}", mv);
    }
}
