//! Merton Jump-Diffusion Model (algebraic identities)
//!
//! Implements the algebraic kernel from:
//! Pythia/Finance/Stochastic/MertonJumpDiffusion.lean
//!
//! In Merton's model, the stock price follows
//! dS/S = (mu - lambda*kappa) dt + sigma dW + J dN
//! where N is a Poisson process and J is log-normal jump size.

/// Compensated drift: the risk-neutral drift under jump diffusion
/// is mu - lambda * kappa where kappa = E[J] - 1.
/// Returns the jump-compensation term: lam * kappa.
///
/// Lean theorem `compensated_drift`:
///   (h : drift = mu - lam * kappa) => mu - drift = lam * kappa
pub fn compensated_drift(mu: f64, lam: f64, kappa: f64) -> f64 {
    let drift = mu - lam * kappa;
    // mu - drift = lam * kappa
    mu - drift
}

/// Total variance over [0,T]:
/// sigma^2 * T + lambda * T * (delta^2 + kappa^2)
///
/// Lean theorem `total_variance`: proves result >= 0 when all inputs >= 0.
pub fn total_variance(sigma_sq: f64, delta_sq: f64, kappa_sq: f64, lam: f64, t: f64) -> f64 {
    sigma_sq * t + lam * t * (delta_sq + kappa_sq)
}

/// Poisson probability of zero jumps: P(N(T) = 0) = exp(-lambda*T).
/// The Lean theorem `no_jump_probability` proves this is strictly positive.
pub fn no_jump_probability(lam: f64, t: f64) -> f64 {
    (-lam * t).exp()
}

/// Jump-adjusted volatility for the n-th term:
/// sigma_n^2 = sigma^2 + n * delta^2 / T.
///
/// Lean theorem `jump_adjusted_vol`: proves sigma_sq <= sigma_n_sq
/// when T > 0, sigma_sq >= 0, delta_sq >= 0.
pub fn jump_adjusted_vol(sigma_sq: f64, delta_sq: f64, n: u64, t: f64) -> f64 {
    sigma_sq + (n as f64) * delta_sq / t
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compensated_drift_basic() {
        let mu = 0.08;
        let lam = 2.0;
        let kappa = 0.03;
        let result = compensated_drift(mu, lam, kappa);
        assert!((result - lam * kappa).abs() < 1e-15);
    }

    #[test]
    fn test_compensated_drift_zero_lambda() {
        let result = compensated_drift(0.05, 0.0, 0.1);
        assert!((result - 0.0).abs() < 1e-15);
    }

    #[test]
    fn test_total_variance_nonneg() {
        let tv = total_variance(0.04, 0.01, 0.001, 3.0, 1.0);
        assert!(tv >= 0.0);
        let expected = 0.04 * 1.0 + 3.0 * 1.0 * (0.01 + 0.001);
        assert!((tv - expected).abs() < 1e-15);
    }

    #[test]
    fn test_total_variance_zero_time() {
        let tv = total_variance(0.04, 0.01, 0.001, 3.0, 0.0);
        assert!((tv - 0.0).abs() < 1e-15);
    }

    #[test]
    fn test_no_jump_probability_positive() {
        let p0 = no_jump_probability(2.0, 1.0);
        assert!(p0 > 0.0);
        assert!((p0 - (-2.0_f64).exp()).abs() < 1e-15);
    }

    #[test]
    fn test_jump_adjusted_vol_monotone() {
        let sigma_sq = 0.04;
        let delta_sq = 0.01;
        let t = 1.0;
        let v0 = jump_adjusted_vol(sigma_sq, delta_sq, 0, t);
        let v1 = jump_adjusted_vol(sigma_sq, delta_sq, 1, t);
        let v5 = jump_adjusted_vol(sigma_sq, delta_sq, 5, t);
        assert!(v0 <= v1);
        assert!(v1 <= v5);
        assert!((v0 - sigma_sq).abs() < 1e-15);
    }
}
