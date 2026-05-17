//! # pythia-options-bspde
//!
//! Verified Black-Scholes PDE operator and self-financing conditions.
//!
//! ## Lean specification (`Pythia.Finance.BlackScholesPDE`)
//!
//! - **BS PDE operator**: theta + (1/2)*sigma^2*S^2*gamma + r*S*delta - r*C (`bsPDEOperator`)
//! - **Theta decompose**: PDE=0 => theta = r*C - r*S*delta - (1/2)*sigma^2*S^2*gamma (`bsPDE_theta_decompose`)
//! - **Gamma term nonneg**: gamma>=0, sigma>=0, S>=0 => gamma contribution >= 0 (`bsPDE_gamma_term_nonneg`)
//! - **Theta <= risk-free**: under PDE=0 and long gamma, theta <= r*(C - S*delta) (`bsPDE_theta_le_riskfree`)
//! - **Linear in theta**: shifting theta shifts operator by same amount (`bsPDEOperator_linear_theta`)
//! - **At expiry**: theta=0 reduces operator (`bsPDEOperator_at_expiry`)

/// Black-Scholes PDE operator:
/// L[C] = theta + (1/2)*sigma^2*S^2*gamma + r*S*delta - r*C.
/// # Lean: `bsPDEOperator`
#[inline(always)]
pub fn bs_pde_operator(theta: f64, delta: f64, gamma: f64, c: f64, s: f64, r: f64, sigma: f64) -> f64 {
    theta + sigma * sigma / 2.0 * s * s * gamma + r * s * delta - r * c
}

/// Gamma term: (1/2)*sigma^2*S^2*gamma.
#[inline(always)]
pub fn gamma_term(sigma: f64, s: f64, gamma: f64) -> f64 {
    sigma * sigma / 2.0 * s * s * gamma
}

/// Check theta decomposition when PDE = 0.
/// # Lean: `bsPDE_theta_decompose`
pub fn check_theta_decompose(theta: f64, delta: f64, gamma: f64, c: f64, s: f64, r: f64, sigma: f64, tol: f64) -> bool {
    let op = bs_pde_operator(theta, delta, gamma, c, s, r, sigma);
    if op.abs() > tol {
        return true; // PDE != 0, property vacuously true
    }
    let expected_theta = r * c - r * s * delta - sigma * sigma / 2.0 * s * s * gamma;
    (theta - expected_theta).abs() < tol
}

/// Check linearity in theta: shifting theta shifts operator by same amount.
/// # Lean: `bsPDEOperator_linear_theta`
pub fn check_linear_theta(theta: f64, dtheta: f64, delta: f64, gamma: f64, c: f64, s: f64, r: f64, sigma: f64, tol: f64) -> bool {
    let shifted = bs_pde_operator(theta + dtheta, delta, gamma, c, s, r, sigma);
    let original = bs_pde_operator(theta, delta, gamma, c, s, r, sigma);
    (shifted - (original + dtheta)).abs() < tol
}

/// Check gamma term nonneg for long gamma, nonneg sigma and S.
/// # Lean: `bsPDE_gamma_term_nonneg`
pub fn check_gamma_term_nonneg(sigma: f64, s: f64, gamma: f64) -> bool {
    sigma >= 0.0 && s >= 0.0 && gamma >= 0.0 && gamma_term(sigma, s, gamma) >= -1e-15
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pde_zero_self_financing() {
        // Construct inputs where PDE = 0:
        // theta = r*C - r*S*delta - (1/2)*sigma^2*S^2*gamma
        let (r, sigma, s, delta, gamma, c) = (0.05, 0.2, 100.0, 0.6, 0.02, 10.0);
        let theta = r * c - r * s * delta - sigma * sigma / 2.0 * s * s * gamma;
        let op = bs_pde_operator(theta, delta, gamma, c, s, r, sigma);
        assert!(op.abs() < 1e-10);
    }

    #[test]
    fn gamma_term_nonneg() {
        assert!(check_gamma_term_nonneg(0.3, 50.0, 0.05));
        assert!(check_gamma_term_nonneg(0.0, 100.0, 1.0));
    }

    #[test]
    fn linear_theta() {
        assert!(check_linear_theta(0.5, 0.3, 0.6, 0.02, 10.0, 100.0, 0.05, 0.2, 1e-10));
    }

    #[test]
    fn at_expiry() {
        // theta=0 reduces operator to gamma + carry - discount
        let (delta, gamma, c, s, r, sigma) = (0.5, 0.03, 5.0, 80.0, 0.03, 0.25);
        let op = bs_pde_operator(0.0, delta, gamma, c, s, r, sigma);
        let expected = sigma * sigma / 2.0 * s * s * gamma + r * s * delta - r * c;
        assert!((op - expected).abs() < 1e-10);
    }

    #[test]
    fn theta_le_riskfree_long_gamma() {
        // Under PDE=0, gamma>=0, theta <= r*(C - S*delta)
        let (r, sigma, s, delta, gamma, c) = (0.05, 0.2, 100.0, 0.6, 0.02, 10.0);
        let theta = r * c - r * s * delta - sigma * sigma / 2.0 * s * s * gamma;
        assert!(theta <= r * (c - s * delta) + 1e-12);
    }

    #[test]
    fn pde_operator_value() {
        let op = bs_pde_operator(1.0, 0.5, 0.03, 10.0, 100.0, 0.05, 0.2);
        // theta + 0.04/2*10000*0.03 + 0.05*100*0.5 - 0.05*10
        // = 1.0 + 6.0 + 2.5 - 0.5 = 9.0
        assert!((op - 9.0).abs() < 1e-10);
    }
}
