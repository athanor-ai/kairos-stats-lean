//! # pythia-options-greeks
//!
//! Verified option Greeks bounds for risk management validation.
//!
//! ## Lean specification (`Pythia.Finance.Options.GreeksBound`)
//!
//! - **Call delta in [0,1]**, put delta in [-1,0] (`call_delta_bounded`, `put_delta_bounded`)
//! - **Gamma, vega nonneg** for vanilla options (`gamma_nonneg`, `vega_nonneg`)
//! - **Put-call parity** on delta, gamma, vega (`delta_parity`, `gamma_parity`, `vega_parity`)
//! - **Theta bounded by -rK** (`theta_lower_bound`)
//! - **BS PDE consistency**: θ + ½σ²S²Γ + rSΔ - rC = 0 (`greeks_pde_check`)

/// Option Greeks for a single position.
#[derive(Debug, Clone, Copy)]
pub struct Greeks {
    pub delta: f64,
    pub gamma: f64,
    pub vega: f64,
    pub theta: f64,
}

/// Validation result for Greeks bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Validity {
    Valid,
    Invalid(&'static str),
}

impl Greeks {
    /// Validate call Greeks against universal bounds.
    ///
    /// # Lean theorems:
    /// - `call_delta_bounded`: 0 ≤ delta ≤ 1
    /// - `gamma_nonneg`: 0 ≤ gamma
    /// - `vega_nonneg`: 0 ≤ vega
    pub fn validate_call(&self) -> Validity {
        if self.delta < 0.0 { return Validity::Invalid("call delta < 0"); }
        if self.delta > 1.0 { return Validity::Invalid("call delta > 1"); }
        if self.gamma < 0.0 { return Validity::Invalid("gamma < 0"); }
        if self.vega < 0.0 { return Validity::Invalid("vega < 0"); }
        Validity::Valid
    }

    /// Validate put Greeks against universal bounds.
    ///
    /// # Lean theorems:
    /// - `put_delta_bounded`: -1 ≤ delta ≤ 0
    /// - `gamma_nonneg`, `vega_nonneg`
    pub fn validate_put(&self) -> Validity {
        if self.delta < -1.0 { return Validity::Invalid("put delta < -1"); }
        if self.delta > 0.0 { return Validity::Invalid("put delta > 0"); }
        if self.gamma < 0.0 { return Validity::Invalid("gamma < 0"); }
        if self.vega < 0.0 { return Validity::Invalid("vega < 0"); }
        Validity::Valid
    }
}

/// Check put-call delta parity: delta_call - delta_put = 1.
///
/// # Lean: `delta_parity`
pub fn check_delta_parity(call_delta: f64, put_delta: f64, tol: f64) -> bool {
    (call_delta - put_delta - 1.0).abs() < tol
}

/// Check gamma parity: call gamma = put gamma.
///
/// # Lean: `gamma_parity`
pub fn check_gamma_parity(call_gamma: f64, put_gamma: f64, tol: f64) -> bool {
    (call_gamma - put_gamma).abs() < tol
}

/// Check vega parity: call vega = put vega.
///
/// # Lean: `vega_parity`
pub fn check_vega_parity(call_vega: f64, put_vega: f64, tol: f64) -> bool {
    (call_vega - put_vega).abs() < tol
}

/// BS PDE consistency: θ + ½σ²S²Γ + rSΔ - rC = 0.
///
/// # Lean: `greeks_pde_check`
pub fn check_bs_pde(
    theta: f64, sigma: f64, spot: f64, gamma: f64,
    rate: f64, delta: f64, option_price: f64, tol: f64,
) -> bool {
    let gamma_term = 0.5 * sigma * sigma * spot * spot * gamma;
    let delta_carry = rate * spot * delta;
    let r_c = rate * option_price;
    (theta + gamma_term + delta_carry - r_c).abs() < tol
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_call_greeks() {
        let g = Greeks { delta: 0.5, gamma: 0.03, vega: 0.2, theta: -0.05 };
        assert_eq!(g.validate_call(), Validity::Valid);
    }

    #[test]
    fn invalid_call_delta_negative() {
        let g = Greeks { delta: -0.1, gamma: 0.03, vega: 0.2, theta: -0.05 };
        assert_ne!(g.validate_call(), Validity::Valid);
    }

    #[test]
    fn valid_put_greeks() {
        let g = Greeks { delta: -0.5, gamma: 0.03, vega: 0.2, theta: -0.04 };
        assert_eq!(g.validate_put(), Validity::Valid);
    }

    #[test]
    fn delta_parity() {
        assert!(check_delta_parity(0.6, -0.4, 1e-10));
        assert!(!check_delta_parity(0.6, -0.5, 1e-10));
    }

    #[test]
    fn gamma_vega_parity() {
        assert!(check_gamma_parity(0.03, 0.03, 1e-10));
        assert!(check_vega_parity(0.2, 0.2, 1e-10));
    }

    #[test]
    fn bs_pde_consistent() {
        let theta = -5.0;
        let sigma = 0.2;
        let spot = 100.0;
        let gamma = 0.03;
        let rate = 0.05;
        let delta = 0.6;
        let gamma_term = 0.5 * sigma * sigma * spot * spot * gamma;
        let delta_carry = rate * spot * delta;
        let option_price = (theta + gamma_term + delta_carry) / rate;
        assert!(check_bs_pde(theta, sigma, spot, gamma, rate, delta, option_price, 1e-10));
    }
}
