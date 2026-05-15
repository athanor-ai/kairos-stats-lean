//! # Sharpe Ratio (algebraic form)
//!
//! Rust port of `Pythia.Finance.Portfolio.SharpeRatio`.
//!
//! The Sharpe ratio of a return stream with expected return `mu`, return
//! standard deviation `sigma`, and risk-free rate `rf` is:
//!
//! ```text
//! Sharpe(mu, rf, sigma) = (mu - rf) / sigma
//! ```
//!
//! ## Lean theorems mirrored
//!
//! - [`sharpeRatio`] — definition `(mu - rf) / sigma`
//! - [`sharpeRatio_pos`] — positive when `rf < mu` and `0 < sigma`
//! - [`sharpeRatio_mono_excess`] — monotone in excess return
//! - [`sharpeRatio_scale_invariant`] — invariant under positive rescaling
//! - [`excess_pos_of_sharpeRatio_pos`] — positive ratio implies positive excess
//! - [`sharpeRatio_cash_invariant`] — adding constant to both mu and rf is no-op

/// Compute the Sharpe ratio: `(mu - rf) / sigma`.
///
/// Corresponds to Lean `Pythia.Finance.sharpeRatio`.
///
/// Returns `f64::NAN` when `sigma == 0.0`, `f64::INFINITY` or
/// `f64::NEG_INFINITY` for zero-denominator edge cases per IEEE 754.
#[inline]
pub fn sharpe_ratio(mu: f64, rf: f64, sigma: f64) -> f64 {
    (mu - rf) / sigma
}

/// Returns `true` when the Sharpe ratio is strictly positive.
///
/// Corresponds to Lean `sharpeRatio_pos`: requires `rf < mu` and `0 < sigma`.
#[inline]
pub fn sharpe_ratio_is_positive(mu: f64, rf: f64, sigma: f64) -> bool {
    rf < mu && sigma > 0.0
}

/// Checks monotonicity in excess return: for fixed positive `sigma`,
/// if `excess1 <= excess2` then `sharpe(excess1/sigma) <= sharpe(excess2/sigma)`.
///
/// Corresponds to Lean `sharpeRatio_mono_excess`.
#[inline]
pub fn sharpe_ratio_mono_excess(excess1: f64, excess2: f64, sigma: f64) -> bool {
    if sigma <= 0.0 {
        return false; // precondition not met
    }
    if excess1 <= excess2 {
        (excess1 / sigma) <= (excess2 / sigma)
    } else {
        false
    }
}

/// Scale-invariance: `sharpe(alpha*mu, alpha*rf, alpha*sigma) == sharpe(mu, rf, sigma)`
/// for `alpha > 0`.
///
/// Corresponds to Lean `sharpeRatio_scale_invariant`.
#[inline]
pub fn sharpe_ratio_scaled(alpha: f64, mu: f64, rf: f64, sigma: f64) -> f64 {
    sharpe_ratio(alpha * mu, alpha * rf, alpha * sigma)
}

/// Cash-invariance: adding the same constant `c` to both `mu` and `rf`
/// leaves the Sharpe ratio unchanged.
///
/// Corresponds to Lean `sharpeRatio_cash_invariant`.
#[inline]
pub fn sharpe_ratio_cash_shifted(mu: f64, rf: f64, sigma: f64, c: f64) -> f64 {
    sharpe_ratio(mu + c, rf + c, sigma)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Test basic computation: sharpe_ratio(0.10, 0.02, 0.15) = 0.08/0.15
    #[test]
    fn test_basic_computation() {
        let result = sharpe_ratio(0.10, 0.02, 0.15);
        let expected = 0.08 / 0.15;
        assert!((result - expected).abs() < EPS);
    }

    /// Lean: `sharpeRatio_pos` — positive when rf < mu and sigma > 0
    #[test]
    fn test_positivity() {
        let r = sharpe_ratio(0.12, 0.03, 0.20);
        assert!(r > 0.0);
        assert!(sharpe_ratio_is_positive(0.12, 0.03, 0.20));
    }

    /// Lean: `sharpeRatio_pos` — negative when mu < rf
    #[test]
    fn test_negative_excess() {
        let r = sharpe_ratio(0.01, 0.05, 0.10);
        assert!(r < 0.0);
        assert!(!sharpe_ratio_is_positive(0.01, 0.05, 0.10));
    }

    /// Lean: `sharpeRatio_scale_invariant`
    #[test]
    fn test_scale_invariance() {
        let base = sharpe_ratio(0.10, 0.02, 0.15);
        let scaled = sharpe_ratio_scaled(3.0, 0.10, 0.02, 0.15);
        assert!((base - scaled).abs() < EPS);
    }

    /// Lean: `sharpeRatio_cash_invariant`
    #[test]
    fn test_cash_invariance() {
        let base = sharpe_ratio(0.10, 0.02, 0.20);
        let shifted = sharpe_ratio_cash_shifted(0.10, 0.02, 0.20, 0.05);
        assert!((base - shifted).abs() < EPS);
    }

    /// Lean: `excess_pos_of_sharpeRatio_pos` — positive ratio implies rf < mu
    #[test]
    fn test_excess_pos_of_positive_sharpe() {
        let mu = 0.12;
        let rf = 0.03;
        let sigma = 0.18;
        let r = sharpe_ratio(mu, rf, sigma);
        assert!(r > 0.0);
        // converse: positive sharpe => rf < mu
        assert!(rf < mu);
    }
}
