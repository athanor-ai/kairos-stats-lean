//! # Stochastic Discount Factor (Pricing Kernel)
//!
//! Rust port of `Pythia.Finance.Stochastic.StochasticDiscount`.
//!
//! The SDF price decomposes as:
//!
//! ```text
//! sdfPrice(m_mean, m_payoff_cov, payoff_mean) = m_mean * payoff_mean + m_payoff_cov
//! ```
//!
//! The Hansen-Jagannathan bound gives:
//!
//! ```text
//! HJ_bound(excess_return, return_vol) = |excess_return| / return_vol
//! ```
//!
//! ## Lean theorems mirrored
//!
//! - [`sdfPrice`] — `m_mean * payoff_mean + m_payoff_cov`
//! - [`sdfPrice_at_zero_cov`] — zero covariance reduces to mean product
//! - [`sdfPrice_decompose`] — unfolds definition
//! - [`hansenJagannathanBound`] — `|excess_return| / return_vol`
//! - [`hansenJagannathanBound_nonneg`] — non-negative when vol > 0
//! - [`hansenJagannathanBound_zero_excess`] — zero when excess return is zero
//! - [`hansenJagannathanBound_mono_excess`] — monotone in |excess_return|

/// Compute the SDF price: `m_mean * payoff_mean + m_payoff_cov`.
///
/// Corresponds to Lean `Pythia.Finance.sdfPrice`.
#[inline]
pub fn sdf_price(m_mean: f64, m_payoff_cov: f64, payoff_mean: f64) -> f64 {
    m_mean * payoff_mean + m_payoff_cov
}

/// Hansen-Jagannathan bound: `|excess_return| / return_vol`.
///
/// Corresponds to Lean `Pythia.Finance.hansenJagannathanBound`.
///
/// Returns `f64::INFINITY` when `return_vol == 0.0` per IEEE 754.
#[inline]
pub fn hansen_jagannathan_bound(excess_return: f64, return_vol: f64) -> f64 {
    excess_return.abs() / return_vol
}

/// At zero covariance, price equals `m_mean * payoff_mean`.
///
/// Corresponds to Lean `sdfPrice_at_zero_cov`.
#[inline]
pub fn sdf_price_at_zero_cov(m_mean: f64, payoff_mean: f64) -> f64 {
    sdf_price(m_mean, 0.0, payoff_mean)
}

/// Returns `true` when the HJ bound is non-negative (requires vol > 0).
///
/// Corresponds to Lean `hansenJagannathanBound_nonneg`.
#[inline]
pub fn hj_bound_is_nonneg(excess_return: f64, return_vol: f64) -> bool {
    return_vol > 0.0 && hansen_jagannathan_bound(excess_return, return_vol) >= 0.0
}

/// Returns `true` when the HJ bound is zero (at zero excess return).
///
/// Corresponds to Lean `hansenJagannathanBound_zero_excess`.
#[inline]
pub fn hj_bound_is_zero_at_zero_excess(return_vol: f64) -> bool {
    let b = hansen_jagannathan_bound(0.0, return_vol);
    b == 0.0
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Basic SDF price computation
    #[test]
    fn test_sdf_price_basic() {
        // m_mean=0.95, cov=-0.02, payoff_mean=105.0
        // price = 0.95*105 + (-0.02) = 99.75 - 0.02 = 99.73
        let p = sdf_price(0.95, -0.02, 105.0);
        let expected = 0.95 * 105.0 + (-0.02);
        assert!((p - expected).abs() < EPS);
    }

    /// Lean: `sdfPrice_at_zero_cov` — zero covariance case
    #[test]
    fn test_zero_cov() {
        let p = sdf_price_at_zero_cov(0.95, 100.0);
        let expected = 0.95 * 100.0;
        assert!((p - expected).abs() < EPS);
    }

    /// Lean: `sdfPrice_decompose` — definition identity
    #[test]
    fn test_sdf_decompose() {
        let m_mean = 0.98;
        let cov = 0.05;
        let payoff_mean = 110.0;
        let p = sdf_price(m_mean, cov, payoff_mean);
        let expected = m_mean * payoff_mean + cov;
        assert!((p - expected).abs() < EPS);
    }

    /// Basic HJ bound computation
    #[test]
    fn test_hj_bound_basic() {
        // excess_return = 0.06, vol = 0.20 => bound = 0.06/0.20 = 0.30
        let b = hansen_jagannathan_bound(0.06, 0.20);
        assert!((b - 0.30).abs() < EPS);
    }

    /// Lean: `hansenJagannathanBound_nonneg` — non-negative when vol > 0
    #[test]
    fn test_hj_bound_nonneg() {
        assert!(hj_bound_is_nonneg(0.05, 0.15));
        assert!(hj_bound_is_nonneg(-0.03, 0.20));
    }

    /// Lean: `hansenJagannathanBound_zero_excess` — zero at zero excess
    #[test]
    fn test_hj_bound_zero_excess() {
        assert!(hj_bound_is_zero_at_zero_excess(0.20));
        let b = hansen_jagannathan_bound(0.0, 0.15);
        assert!((b - 0.0).abs() < EPS);
    }
}
