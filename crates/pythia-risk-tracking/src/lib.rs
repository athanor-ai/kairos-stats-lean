//! # pythia-risk-tracking
//!
//! Verified tracking error (benchmark-relative volatility) properties.
//!
//! ## Lean specification (`Pythia.Finance.Risk.TrackingError`)
//!
//! - **Variance non-negativity**: `trackingVariance_nonneg` — max(V, 0) >= 0
//! - **TE non-negativity**: `trackingError_nonneg` — sqrt(trackingVariance) >= 0
//! - **Square link**: `trackingError_sq` — TE^2 = trackingVariance
//! - **Zero active return**: `trackingVariance_zero_active_return` — V=0 => TV=0

/// Tracking variance: max(V, 0) — the clipped non-negative variance parameter.
///
/// # Lean: `trackingVariance`
#[inline(always)]
pub fn tracking_variance(v: f64) -> f64 {
    v.max(0.0)
}

/// Tracking error: sqrt(trackingVariance(V)).
///
/// # Lean: `trackingError`
#[inline(always)]
pub fn tracking_error(v: f64) -> f64 {
    tracking_variance(v).sqrt()
}

/// Square link: tracking_error(V)^2 = tracking_variance(V).
///
/// # Lean: `trackingError_sq`
#[inline(always)]
pub fn tracking_error_squared(v: f64) -> f64 {
    let te = tracking_error(v);
    te * te
}

/// Empirical tracking variance from an active-return series.
/// Uses population variance: sum(e_i^2)/n - (sum(e_i)/n)^2.
#[inline]
pub fn empirical_tracking_variance(active_returns: &[f64]) -> f64 {
    if active_returns.is_empty() {
        return 0.0;
    }
    let n = active_returns.len() as f64;
    let mean = active_returns.iter().sum::<f64>() / n;
    let mse = active_returns.iter().map(|e| e * e).sum::<f64>() / n;
    tracking_variance(mse - mean * mean)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Lean: `trackingVariance_nonneg` — variance is always non-negative
    #[test]
    fn test_variance_nonneg() {
        assert!(tracking_variance(5.0) >= 0.0);
        assert!(tracking_variance(0.0) >= 0.0);
        assert!(tracking_variance(-3.0) >= 0.0);
    }

    /// Lean: `trackingError_nonneg` — TE is always non-negative
    #[test]
    fn test_error_nonneg() {
        assert!(tracking_error(4.0) >= 0.0);
        assert!(tracking_error(0.0) >= 0.0);
        assert!(tracking_error(-2.0) >= 0.0);
    }

    /// Lean: `trackingError_sq` — TE^2 = trackingVariance
    #[test]
    fn test_square_link() {
        let v = 9.0;
        let tv = tracking_variance(v);
        let te_sq = tracking_error_squared(v);
        assert!((te_sq - tv).abs() < EPS);
    }

    /// Lean: `trackingVariance_zero_active_return` — V=0 => TV=0
    #[test]
    fn test_zero_active_return() {
        assert!((tracking_variance(0.0)).abs() < EPS);
        assert!((tracking_error(0.0)).abs() < EPS);
    }

    /// Square link with negative input (clips to 0)
    #[test]
    fn test_square_link_negative() {
        let v = -5.0;
        let tv = tracking_variance(v);
        let te_sq = tracking_error_squared(v);
        assert!((te_sq - tv).abs() < EPS);
        assert!(tv.abs() < EPS); // clipped to 0
    }

    /// Empirical variance of constant series is zero
    #[test]
    fn test_empirical_constant_series() {
        let series = vec![0.01, 0.01, 0.01, 0.01];
        let tv = empirical_tracking_variance(&series);
        assert!(tv.abs() < EPS);
    }
}
