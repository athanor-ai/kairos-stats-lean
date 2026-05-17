//! # pythia-risk-entropy
//!
//! Verified entropic risk measure.
//!
//! ## Lean specification (`Pythia.Finance.EntropyRisk`)
//!
//! - **Entropic risk**: rho_theta(X) = (1/theta) * log(MGF) (`entropicRisk`)
//! - **Well-defined**: theta > 0, MGF > 0 implies finite result (`entropic_risk_finite`)
//! - **Constant**: rho_theta(c) = -c when MGF = exp(-theta*c) (`entropic_risk_constant`)
//! - **KL penalty nonneg**: (1/theta)*KL >= 0 for theta > 0, KL >= 0 (`kl_penalty_nonneg`)

/// Entropic risk measure: rho_theta(X) = (1/theta) * ln(mgf_val).
/// # Lean: `entropicRisk`
#[inline(always)]
pub fn entropic_risk(theta: f64, mgf_val: f64) -> f64 {
    (1.0 / theta) * mgf_val.ln()
}

/// Entropic risk of a constant: if X = c a.s., MGF = exp(-theta*c),
/// so rho = (1/theta)*ln(exp(-theta*c)) = -c.
/// # Lean: `entropic_risk_constant`
#[inline(always)]
pub fn entropic_risk_constant(theta: f64, c: f64) -> f64 {
    entropic_risk(theta, (-theta * c).exp())
}

/// KL divergence penalty: (1/theta) * kl.
/// # Lean: `kl_penalty_nonneg`
#[inline(always)]
pub fn kl_penalty(theta: f64, kl: f64) -> f64 {
    (1.0 / theta) * kl
}

/// Check that entropic risk of a constant equals -c.
/// # Lean: `entropic_risk_constant`
pub fn check_constant_property(theta: f64, c: f64, tol: f64) -> bool {
    (entropic_risk_constant(theta, c) - (-c)).abs() < tol
}

/// Check KL penalty is nonneg for theta > 0, kl >= 0.
/// # Lean: `kl_penalty_nonneg`
pub fn check_kl_penalty_nonneg(theta: f64, kl: f64) -> bool {
    theta > 0.0 && kl >= 0.0 && kl_penalty(theta, kl) >= 0.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_risk_zero() {
        // rho_theta(0) = 0 since MGF = exp(0) = 1, ln(1) = 0
        let rho = entropic_risk(1.0, 1.0);
        assert!((rho - 0.0).abs() < 1e-12);
    }

    #[test]
    fn constant_risk_positive_c() {
        assert!(check_constant_property(2.0, 5.0, 1e-10));
    }

    #[test]
    fn constant_risk_negative_c() {
        assert!(check_constant_property(0.5, -3.0, 1e-10));
    }

    #[test]
    fn kl_penalty_nonneg_basic() {
        assert!(check_kl_penalty_nonneg(1.0, 0.0));
        assert!(check_kl_penalty_nonneg(0.5, 2.3));
    }

    #[test]
    fn entropic_risk_finite_positive_inputs() {
        // For theta > 0 and mgf_val > 0, result is finite
        let rho = entropic_risk(1.5, 2.0);
        assert!(rho.is_finite());
    }

    #[test]
    fn entropic_risk_monotone_in_mgf() {
        // Higher MGF -> higher risk (since ln is monotone)
        let theta = 1.0;
        assert!(entropic_risk(theta, 1.0) < entropic_risk(theta, 2.0));
    }
}
