//! # pythia-risk-correlation
//!
//! Verified correlation risk properties.
//!
//! ## Lean specification (`Pythia.Finance.Risk.CorrelationRisk`)
//!
//! - **Correlation in [-1,1]** (`correlation_bounded`)
//! - **Zero corr reduces var** (`uncorrelated_reduces_var`)
//! - **Negative corr reduces more** (`negative_corr_reduces_more`)
//! - **Stress increases var** (`stress_increases_var`)

/// Portfolio variance: w1²v1 + w2²v2 + 2*w1*w2*cov.
pub fn portfolio_variance(w1: f64, v1: f64, w2: f64, v2: f64, rho: f64) -> f64 {
    let s1 = v1.sqrt();
    let s2 = v2.sqrt();
    w1 * w1 * v1 + w2 * w2 * v2 + 2.0 * w1 * w2 * rho * s1 * s2
}

/// Check correlation bounded.
/// # Lean: `correlation_bounded`
pub fn is_valid_correlation(rho: f64) -> bool {
    rho >= -1.0 - 1e-12 && rho <= 1.0 + 1e-12
}

/// Diversification benefit: var(perfect_corr) - var(actual).
pub fn diversification_benefit(w1: f64, v1: f64, w2: f64, v2: f64, rho: f64) -> f64 {
    portfolio_variance(w1, v1, w2, v2, 1.0) - portfolio_variance(w1, v1, w2, v2, rho)
}

/// Stress impact: increase in variance from correlation rising.
/// # Lean: `stress_increases_var`
pub fn stress_var_increase(w1: f64, v1: f64, w2: f64, v2: f64, rho_normal: f64, rho_stress: f64) -> f64 {
    portfolio_variance(w1, v1, w2, v2, rho_stress) - portfolio_variance(w1, v1, w2, v2, rho_normal)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correlation_valid() {
        assert!(is_valid_correlation(0.5));
        assert!(!is_valid_correlation(1.5));
    }

    #[test]
    fn zero_corr_less_than_perfect() {
        let v_perf = portfolio_variance(0.5, 0.04, 0.5, 0.04, 1.0);
        let v_zero = portfolio_variance(0.5, 0.04, 0.5, 0.04, 0.0);
        assert!(v_zero < v_perf);
    }

    #[test]
    fn negative_corr_less_than_zero() {
        let v_zero = portfolio_variance(0.5, 0.04, 0.5, 0.04, 0.0);
        let v_neg = portfolio_variance(0.5, 0.04, 0.5, 0.04, -0.5);
        assert!(v_neg < v_zero);
    }

    #[test]
    fn stress_increases_var() {
        let inc = stress_var_increase(0.5, 0.04, 0.5, 0.04, 0.3, 0.8);
        assert!(inc > 0.0);
    }

    #[test]
    fn diversification_nonneg() {
        let ben = diversification_benefit(0.5, 0.04, 0.5, 0.04, 0.3);
        assert!(ben >= 0.0);
    }
}
