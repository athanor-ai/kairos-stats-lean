//! # GARCH(1,1) Variance Update + Stationarity Condition
//!
//! Rust port of `Pythia.Finance.Risk.GARCHUpdate`.
//!
//! The GARCH(1,1) model updates conditional variance via:
//!
//! ```text
//! sigma_sq_t = omega + alpha * eps^2 + beta * sigma_sq_{t-1}
//! ```
//!
//! with non-negativity parameters `omega >= 0, alpha >= 0, beta >= 0` and the
//! covariance-stationarity condition `alpha + beta < 1`. Under stationarity,
//! the unconditional variance is `sigma_sq_inf = omega / (1 - alpha - beta)`.
//!
//! ## Lean theorems mirrored
//!
//! - [`garchUpdate`] — definition `omega + alpha*eps^2 + beta*sigma_sq`
//! - [`garchUpdate_nonneg`] — non-negativity preserved
//! - [`garchStationaryVariance`] — `omega / (1 - alpha - beta)`
//! - [`garchStationaryVariance_pos`] — positive under omega > 0 and stationarity
//! - [`garchStationaryVariance_recurrence`] — fixed-point equation

/// GARCH(1,1) conditional-variance update:
/// `sigma_sq_t = omega + alpha * eps^2 + beta * sigma_sq_{t-1}`.
///
/// Corresponds to Lean `Pythia.Finance.garchUpdate`.
#[inline]
pub fn garch_update(omega: f64, alpha: f64, beta: f64, eps: f64, sigma_sq: f64) -> f64 {
    omega + alpha * eps * eps + beta * sigma_sq
}

/// Returns `true` when the GARCH update preserves non-negativity.
///
/// Corresponds to Lean `garchUpdate_nonneg`: requires all params and
/// previous variance non-negative.
#[inline]
pub fn garch_update_nonneg(omega: f64, alpha: f64, beta: f64, sigma_sq: f64) -> bool {
    omega >= 0.0 && alpha >= 0.0 && beta >= 0.0 && sigma_sq >= 0.0
}

/// Stationary unconditional variance under GARCH(1,1):
/// `omega / (1 - alpha - beta)`.
///
/// Corresponds to Lean `Pythia.Finance.garchStationaryVariance`.
///
/// # Panics
///
/// Panics if `alpha + beta >= 1` (stationarity violated).
#[inline]
pub fn garch_stationary_variance(omega: f64, alpha: f64, beta: f64) -> f64 {
    assert!(
        alpha + beta < 1.0,
        "stationarity requires alpha + beta < 1, got {}",
        alpha + beta
    );
    omega / (1.0 - alpha - beta)
}

/// Returns `true` when the GARCH(1,1) process is covariance-stationary.
///
/// Stationarity condition: `alpha + beta < 1`.
#[inline]
pub fn is_stationary(alpha: f64, beta: f64) -> bool {
    alpha + beta < 1.0
}

/// Check if the stationary variance satisfies the fixed-point recurrence:
/// `sigma_sq_inf = omega + (alpha + beta) * sigma_sq_inf`.
///
/// Corresponds to Lean `garchStationaryVariance_recurrence`.
///
/// Returns the absolute error between both sides.
#[inline]
pub fn garch_recurrence_error(omega: f64, alpha: f64, beta: f64) -> f64 {
    let sv = garch_stationary_variance(omega, alpha, beta);
    let rhs = omega + (alpha + beta) * sv;
    (sv - rhs).abs()
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Test basic GARCH update computation
    #[test]
    fn test_basic_update() {
        // omega=0.00001, alpha=0.05, beta=0.90, eps=0.02, sigma_sq=0.0004
        let result = garch_update(0.00001, 0.05, 0.90, 0.02, 0.0004);
        let expected = 0.00001 + 0.05 * 0.0004 + 0.90 * 0.0004;
        assert!((result - expected).abs() < EPS);
    }

    /// Lean: `garchUpdate_nonneg` — non-negativity preserved
    #[test]
    fn test_update_nonneg() {
        let result = garch_update(0.00001, 0.05, 0.90, -0.03, 0.0004);
        assert!(result >= 0.0);
        assert!(garch_update_nonneg(0.00001, 0.05, 0.90, 0.0004));
    }

    /// Lean: `garchStationaryVariance_pos` — positive under omega > 0 and stationarity
    #[test]
    fn test_stationary_variance_pos() {
        let sv = garch_stationary_variance(0.00001, 0.05, 0.90);
        assert!(sv > 0.0);
    }

    /// Lean: `garchStationaryVariance_recurrence` — fixed-point equation
    #[test]
    fn test_recurrence() {
        let err = garch_recurrence_error(0.00001, 0.05, 0.90);
        assert!(err < EPS);
    }

    /// Stationarity check
    #[test]
    fn test_stationarity() {
        assert!(is_stationary(0.05, 0.90));
        assert!(!is_stationary(0.1, 0.95));
        assert!(!is_stationary(0.5, 0.5));
    }

    /// Update with zero innovation reduces to omega + beta*sigma_sq
    #[test]
    fn test_zero_innovation() {
        let omega = 0.00002;
        let beta = 0.85;
        let sigma_sq = 0.0003;
        let result = garch_update(omega, 0.05, beta, 0.0, sigma_sq);
        let expected = omega + beta * sigma_sq;
        assert!((result - expected).abs() < EPS);
    }
}
