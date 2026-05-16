//! # pythia-portfolio-meanvar2
//!
//! Mean-variance utility (Markowitz 1952) with diversification properties.
//!
//! ## Lean specification (`Pythia.Finance.MeanVarianceUtility`)
//!
//! - **MV Utility**: U(mu, sigma_sq) = mu - (gamma/2) * sigma_sq (`mvUtility`)
//! - **Zero-variance**: U(gamma, mu, 0) = mu (`mvUtility_zero_variance`)
//! - **Bounded by mean**: U <= mu for gamma > 0, sigma_sq >= 0 (`mvUtility_le_mean`)
//! - **Monotone in return**: mu1 <= mu2 => U(mu1) <= U(mu2) (`mvUtility_mono_return`)
//! - **Antitone in variance**: sig1 <= sig2 => U(sig2) <= U(sig1) (`mvUtility_antitone_variance`)
//! - **Antitone in risk aversion**: gamma1 <= gamma2 => U(gamma2) <= U(gamma1) (`mvUtility_antitone_risk_aversion`)
//! - **Equals mean iff**: U = mu iff gamma*sigma_sq = 0 (`mvUtility_eq_mean_iff_zero_variance_or_zero_gamma`)

/// Mean-variance utility: U(mu, sigma_sq) = mu - (gamma / 2) * sigma_sq.
///
/// - `gamma`: risk aversion parameter (should be >= 0)
/// - `mu`: expected portfolio return
/// - `sigma_sq`: portfolio return variance (should be >= 0)
///
/// # Lean: `mvUtility`
pub fn mv_utility(gamma: f64, mu: f64, sigma_sq: f64) -> f64 {
    mu - (gamma / 2.0) * sigma_sq
}

/// Check if utility equals mean (risk penalty vanishes).
///
/// Returns true iff gamma * sigma_sq == 0 (within tolerance).
///
/// # Lean: `mvUtility_eq_mean_iff_zero_variance_or_zero_gamma`
pub fn utility_equals_mean(gamma: f64, sigma_sq: f64) -> bool {
    (gamma * sigma_sq).abs() < 1e-12
}

/// Certainty equivalent: the risk-free return that gives the same utility
/// as the risky portfolio. For MV utility, this is exactly mv_utility itself.
pub fn certainty_equivalent(gamma: f64, mu: f64, sigma_sq: f64) -> f64 {
    mv_utility(gamma, mu, sigma_sq)
}

/// Risk premium: the excess return required to compensate for variance.
/// risk_premium = (gamma / 2) * sigma_sq.
pub fn risk_premium(gamma: f64, sigma_sq: f64) -> f64 {
    (gamma / 2.0) * sigma_sq
}

/// Diversification benefit: difference in utility between a diversified
/// portfolio (with variance sigma_sq_div) and a concentrated one
/// (sigma_sq_conc). Positive when sigma_sq_div < sigma_sq_conc.
///
/// Lean basis: `mvUtility_antitone_variance` proves U(sig2) <= U(sig1) when sig1 <= sig2.
pub fn diversification_benefit(gamma: f64, mu: f64, sigma_sq_conc: f64, sigma_sq_div: f64) -> f64 {
    mv_utility(gamma, mu, sigma_sq_div) - mv_utility(gamma, mu, sigma_sq_conc)
}

/// Optimal variance for a target utility level.
/// Given target U, solve for sigma_sq: sigma_sq = 2*(mu - U) / gamma.
/// Returns None if gamma <= 0 or if result would be negative.
pub fn target_variance(gamma: f64, mu: f64, target_utility: f64) -> Option<f64> {
    if gamma <= 0.0 {
        return None;
    }
    let sigma_sq = 2.0 * (mu - target_utility) / gamma;
    if sigma_sq < 0.0 {
        None
    } else {
        Some(sigma_sq)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_variance_equals_mean() {
        // Lean: `mvUtility_zero_variance`
        let u = mv_utility(2.0, 0.08, 0.0);
        assert!((u - 0.08).abs() < 1e-12);
    }

    #[test]
    fn utility_le_mean() {
        // Lean: `mvUtility_le_mean`
        let gamma = 3.0;
        let mu = 0.1;
        let sigma_sq = 0.04;
        let u = mv_utility(gamma, mu, sigma_sq);
        assert!(u <= mu + 1e-12);
    }

    #[test]
    fn monotone_in_return() {
        // Lean: `mvUtility_mono_return`
        let gamma = 2.0;
        let sigma_sq = 0.03;
        let u1 = mv_utility(gamma, 0.05, sigma_sq);
        let u2 = mv_utility(gamma, 0.10, sigma_sq);
        assert!(u1 <= u2 + 1e-12);
    }

    #[test]
    fn antitone_in_variance() {
        // Lean: `mvUtility_antitone_variance`
        let gamma = 2.0;
        let mu = 0.08;
        let u1 = mv_utility(gamma, mu, 0.02);
        let u2 = mv_utility(gamma, mu, 0.05);
        assert!(u2 <= u1 + 1e-12);
    }

    #[test]
    fn antitone_in_risk_aversion() {
        // Lean: `mvUtility_antitone_risk_aversion`
        let mu = 0.08;
        let sigma_sq = 0.04;
        let u1 = mv_utility(1.0, mu, sigma_sq);
        let u2 = mv_utility(5.0, mu, sigma_sq);
        assert!(u2 <= u1 + 1e-12);
    }

    #[test]
    fn diversification_benefit_positive() {
        let gamma = 3.0;
        let mu = 0.08;
        // Diversified has lower variance => higher utility => positive benefit
        let benefit = diversification_benefit(gamma, mu, 0.05, 0.02);
        assert!(benefit > 0.0);
    }

    #[test]
    fn risk_premium_nonneg() {
        let rp = risk_premium(2.0, 0.04);
        assert!(rp >= 0.0);
        assert!((rp - 0.04).abs() < 1e-12); // (2/2)*0.04 = 0.04
    }
}
