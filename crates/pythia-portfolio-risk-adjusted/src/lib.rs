//! # pythia-portfolio-risk-adjusted
//!
//! Rust port of `Pythia.Finance.Portfolio.RiskAdjustedReturn`.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.RiskAdjustedReturn`)
//!
//! - **excessReturn**: `mu - rf` (`excessReturn`)
//! - **excessReturn_pos_iff**: `0 < excessReturn mu rf <-> rf < mu`
//! - **certaintyEquiv**: `mu - (gamma/2) * sigma_sq` (`certaintyEquiv`)
//! - **certaintyEquiv_le_mean**: CE <= mu for gamma >= 0, sigma_sq >= 0
//! - **certaintyEquiv_mono_return**: monotone in mu
//! - **certaintyEquiv_antitone_risk**: antitone in gamma

/// Excess return over the risk-free rate.
///
/// # Lean: `excessReturn`
#[inline]
pub fn excess_return(mu: f64, rf: f64) -> f64 {
    mu - rf
}

/// Certainty equivalent under quadratic risk penalty.
///
/// CE = mu - (gamma / 2) * sigma_sq
///
/// # Lean: `certaintyEquiv`
#[inline]
pub fn certainty_equiv(mu: f64, gamma: f64, sigma_sq: f64) -> f64 {
    mu - (gamma / 2.0) * sigma_sq
}

/// Check whether excess return is positive (rf < mu).
///
/// # Lean: `excessReturn_pos_iff`
#[inline]
pub fn excess_return_is_positive(mu: f64, rf: f64) -> bool {
    rf < mu
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Basic excess return computation
    #[test]
    fn test_excess_return_basic() {
        let er = excess_return(0.12, 0.03);
        assert!((er - 0.09).abs() < EPS);
    }

    /// Lean: `excessReturn_pos_iff` — positive when rf < mu
    #[test]
    fn test_excess_return_pos() {
        assert!(excess_return(0.10, 0.03) > 0.0);
        assert!(excess_return_is_positive(0.10, 0.03));
    }

    /// Lean: `excessReturn_pos_iff` — negative when mu < rf
    #[test]
    fn test_excess_return_neg() {
        assert!(excess_return(0.01, 0.05) < 0.0);
        assert!(!excess_return_is_positive(0.01, 0.05));
    }

    /// Lean: `certaintyEquiv_le_mean` — CE <= mu for nonneg gamma, sigma_sq
    #[test]
    fn test_ce_le_mean() {
        let mu = 0.10;
        let gamma = 2.0;
        let sigma_sq = 0.04;
        let ce = certainty_equiv(mu, gamma, sigma_sq);
        assert!(ce <= mu);
    }

    /// Lean: `certaintyEquiv_mono_return` — higher mu -> higher CE
    #[test]
    fn test_ce_mono_return() {
        let gamma = 3.0;
        let sigma_sq = 0.09;
        let ce1 = certainty_equiv(0.05, gamma, sigma_sq);
        let ce2 = certainty_equiv(0.15, gamma, sigma_sq);
        assert!(ce1 < ce2);
    }

    /// Lean: `certaintyEquiv_antitone_risk` — higher gamma -> lower CE
    #[test]
    fn test_ce_antitone_risk() {
        let mu = 0.12;
        let sigma_sq = 0.04;
        let ce_low = certainty_equiv(mu, 1.0, sigma_sq);
        let ce_high = certainty_equiv(mu, 5.0, sigma_sq);
        assert!(ce_high < ce_low);
    }
}
