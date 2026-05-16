//! CAPM Beta (algebraic identities)
//!
//! Implements the algebraic kernel from:
//! Pythia/Finance/Portfolio/CAPMBeta.lean
//!
//! beta_i = Cov(R_i, R_m) / Var(R_m)
//! E[R_i] = R_f + beta_i * (E[R_m] - R_f)

/// CAPM expected return: E[R_i] = R_f + beta * (E[R_m] - R_f).
/// Returns E[R_i].
pub fn capm_expected_return(rf: f64, beta: f64, erm: f64) -> f64 {
    rf + beta * (erm - rf)
}

/// Excess return: E[R_i] - R_f = beta * (E[R_m] - R_f).
///
/// Lean theorem `capm_expected_return`: proves ERi - Rf = beta * (ERm - Rf).
pub fn capm_excess_return(rf: f64, beta: f64, erm: f64) -> f64 {
    beta * (erm - rf)
}

/// Risk decomposition: Var(R_i) = beta^2 * Var(R_m) + Var(epsilon).
/// Returns (systematic_var, idiosyncratic_var).
///
/// Lean theorem `risk_decomposition`: proves beta_sq * var_m <= var_i.
pub fn risk_decomposition(beta_sq: f64, var_m: f64, var_eps: f64) -> (f64, f64) {
    let systematic = beta_sq * var_m;
    (systematic, var_eps)
}

/// R-squared = systematic variance / total variance.
/// Returns R^2 in [0, 1] when inputs are valid.
///
/// Lean theorem `r_squared_bound`: proves beta_sq * var_m / var_i <= 1.
pub fn r_squared(beta_sq: f64, var_m: f64, var_i: f64) -> f64 {
    beta_sq * var_m / var_i
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: capm_expected_return: ERi - Rf = beta * (ERm - Rf)
    #[test]
    fn test_capm_excess_return() {
        let rf = 0.03;
        let beta = 1.5;
        let erm = 0.10;
        let eri = capm_expected_return(rf, beta, erm);
        let excess = eri - rf;
        let expected_excess = beta * (erm - rf);
        assert!((excess - expected_excess).abs() < 1e-15);
    }

    /// Lean: zero_beta_return: beta=0 => E[R_i] = R_f
    #[test]
    fn test_zero_beta() {
        let rf = 0.03;
        let erm = 0.10;
        let eri = capm_expected_return(rf, 0.0, erm);
        assert!((eri - rf).abs() < 1e-15);
    }

    /// Lean: market_beta: beta=1 => E[R_i] = E[R_m]
    #[test]
    fn test_market_beta() {
        let rf = 0.03;
        let erm = 0.10;
        let eri = capm_expected_return(rf, 1.0, erm);
        assert!((eri - erm).abs() < 1e-15);
    }

    /// Lean: risk_decomposition: systematic <= total
    #[test]
    fn test_risk_decomposition() {
        let beta_sq = 1.5_f64.powi(2);
        let var_m = 0.04;
        let var_eps = 0.02;
        let (systematic, idio) = risk_decomposition(beta_sq, var_m, var_eps);
        let total = systematic + idio;
        assert!(systematic <= total);
    }

    /// Lean: r_squared_bound: R^2 <= 1 when systematic <= total
    #[test]
    fn test_r_squared_bound() {
        let beta_sq = 1.2_f64.powi(2);
        let var_m = 0.04;
        let var_eps = 0.03;
        let var_i = beta_sq * var_m + var_eps;
        let rsq = r_squared(beta_sq, var_m, var_i);
        assert!(rsq <= 1.0);
        assert!(rsq >= 0.0);
    }

    /// Consistency: excess_return matches expected_return - rf
    #[test]
    fn test_consistency() {
        let rf = 0.02;
        let beta = 0.8;
        let erm = 0.12;
        let eri = capm_expected_return(rf, beta, erm);
        let excess = capm_excess_return(rf, beta, erm);
        assert!((eri - rf - excess).abs() < 1e-15);
    }
}
