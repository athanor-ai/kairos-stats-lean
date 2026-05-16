//! # pythia-credit-spread
//!
//! Verified credit spread decomposition under risk-neutral pricing.
//!
//! ## Lean specification (`Pythia.Finance.Credit.CreditSpread`)
//!
//! - **Spread nonneg**: `creditSpread(y_risky, y_rf) >= 0` when `y_risky >= y_rf`
//! - **Spread zero iff**: spread = 0 iff `y_risky = y_rf`
//! - **Expected loss nonneg**: `pd * lgd >= 0` for `pd, lgd >= 0`
//! - **Expected loss bounded**: `pd * lgd <= lgd` when `pd <= 1`
//! - **Expected loss monotone in pd**: higher pd -> higher expected loss
//! - **Decomposition identity**: `spread = expectedLoss + riskPremium`

/// Credit spread: yield difference between a risky bond and a risk-free bond.
///
/// # Lean: `creditSpread`
#[inline(always)]
pub fn credit_spread(y_risky: f64, y_rf: f64) -> f64 {
    y_risky - y_rf
}

/// Expected loss under risk-neutral pricing: `pd * lgd`.
///
/// # Lean: `expectedLoss`
#[inline(always)]
pub fn expected_loss(pd: f64, lgd: f64) -> f64 {
    pd * lgd
}

/// Risk premium: portion of credit spread in excess of expected loss.
///
/// # Lean: `riskPremium`
#[inline(always)]
pub fn risk_premium(spread: f64, pd: f64, lgd: f64) -> f64 {
    spread - expected_loss(pd, lgd)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spread_nonneg_when_risky_exceeds_rf() {
        assert!(credit_spread(0.05, 0.02) >= 0.0);
    }

    #[test]
    fn spread_zero_when_equal() {
        assert_eq!(credit_spread(0.03, 0.03), 0.0);
    }

    #[test]
    fn spread_nonzero_when_different() {
        assert_ne!(credit_spread(0.05, 0.03), 0.0);
    }

    #[test]
    fn expected_loss_nonneg() {
        assert!(expected_loss(0.02, 0.6) >= 0.0);
    }

    #[test]
    fn expected_loss_bounded_by_lgd() {
        let pd = 0.8;
        let lgd = 0.6;
        assert!(expected_loss(pd, lgd) <= lgd);
    }

    #[test]
    fn decomposition_identity() {
        let y_risky = 0.07;
        let y_rf = 0.02;
        let pd = 0.03;
        let lgd = 0.4;
        let spread = credit_spread(y_risky, y_rf);
        let rp = risk_premium(spread, pd, lgd);
        let el = expected_loss(pd, lgd);
        assert!((spread - (el + rp)).abs() < 1e-15);
    }
}
