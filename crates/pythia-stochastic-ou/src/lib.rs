//! # pythia-stochastic-ou
//!
//! Verified Ornstein-Uhlenbeck mean-reverting process.
//!
//! ## Lean specification (`Pythia.Finance.OrnsteinUhlenbeck`)
//!
//! - **Closed form**: X_t = X0*exp(-θt) + μ*(1-exp(-θt)) + noise (`ouTerminal`)
//! - **Boundary at t=0**: ouTerminal X0 μ θ 0 0 = X0 (`ouTerminal_zero_time`)
//! - **At mean**: starting at μ stays at μ (`ouTerminal_at_mean`)
//! - **Linear in noise** (`ouTerminal_linear_noise`)

/// OU terminal value: X0*exp(-θt) + μ*(1-exp(-θt)) + noise.
/// # Lean: `ouTerminal`
#[inline(always)]
pub fn ou_terminal(x0: f64, mu: f64, theta: f64, t: f64, noise: f64) -> f64 {
    let decay = (-theta * t).exp();
    x0 * decay + mu * (1.0 - decay) + noise
}

/// OU half-life: ln(2) / θ.
pub fn ou_half_life(theta: f64) -> f64 {
    assert!(theta > 0.0);
    (2.0_f64).ln() / theta
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_time_returns_x0() {
        assert!((ou_terminal(100.0, 50.0, 2.0, 0.0, 0.0) - 100.0).abs() < 1e-10);
    }

    #[test]
    fn at_mean_stays() {
        assert!((ou_terminal(50.0, 50.0, 2.0, 5.0, 0.0) - 50.0).abs() < 1e-10);
    }

    #[test]
    fn mean_reverts() {
        let x = ou_terminal(100.0, 50.0, 2.0, 10.0, 0.0);
        assert!((x - 50.0).abs() < 1.0); // should be very close to mu
    }

    #[test]
    fn linear_in_noise() {
        let base = ou_terminal(100.0, 50.0, 2.0, 1.0, 0.0);
        let with_noise = ou_terminal(100.0, 50.0, 2.0, 1.0, 5.0);
        assert!((with_noise - base - 5.0).abs() < 1e-10);
    }

    #[test]
    fn half_life() {
        let hl = ou_half_life(2.0);
        let x = ou_terminal(100.0, 0.0, 2.0, hl, 0.0);
        assert!((x - 50.0).abs() < 1e-8);
    }
}
