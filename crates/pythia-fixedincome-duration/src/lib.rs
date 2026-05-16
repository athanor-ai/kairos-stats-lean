//! # Bond Convexity and Modified Duration (price-yield sensitivity kernel)
//!
//! Rust port of `Pythia.Finance.FixedIncome.ConvexityDuration`.
//!
//! For a generic price-yield function `P(y) = B * exp(-D*y + C*y^2/2)`
//! (a second-order log-affine approximation), the log-price is:
//!
//! ```text
//! bondLogPrice(logB, D, C, y) = logB - D*y + C*y^2/2
//! ```
//!
//! where `D` is the modified duration and `C` is the convexity.
//!
//! ## Lean theorems mirrored
//!
//! - [`bondLogPrice`] — definition `logB - D*y + C*y^2/2`
//! - [`bondLogPrice_at_zero_y`] — at `y = 0` reduces to `logB`
//! - [`bondLogPrice_zero_convexity`] — `C = 0` gives `logB - D*y`
//! - [`bondLogPrice_linear_logB`] — shifting `logB` by delta shifts output by delta

/// Compute the log-bond-price under a second-order yield expansion:
/// `logB - D*y + C*y^2/2`.
///
/// Corresponds to Lean `Pythia.Finance.bondLogPrice`.
#[inline]
pub fn bond_log_price(log_b: f64, d: f64, c: f64, y: f64) -> f64 {
    log_b - d * y + c * y * y / 2.0
}

/// At zero yield, the log-price equals `logB`.
///
/// Corresponds to Lean `bondLogPrice_at_zero_y`.
#[inline]
pub fn bond_log_price_at_zero_y(log_b: f64, d: f64, c: f64) -> f64 {
    bond_log_price(log_b, d, c, 0.0)
}

/// With zero convexity (`C = 0`), the log-price is linear in yield:
/// `logB - D*y`.
///
/// Corresponds to Lean `bondLogPrice_zero_convexity`.
#[inline]
pub fn bond_log_price_zero_convexity(log_b: f64, d: f64, y: f64) -> f64 {
    bond_log_price(log_b, d, 0.0, y)
}

/// Linearity in log-base-price: shifting `logB` by `delta` shifts
/// the log-price by `delta`.
///
/// Corresponds to Lean `bondLogPrice_linear_logB`.
#[inline]
pub fn bond_log_price_shifted(log_b: f64, delta: f64, d: f64, c: f64, y: f64) -> f64 {
    bond_log_price(log_b + delta, d, c, y)
}

/// First-order yield sensitivity (negative of modified duration):
/// `d(logP)/dy = -D + C*y`.
#[inline]
pub fn bond_log_price_deriv(d: f64, c: f64, y: f64) -> f64 {
    -d + c * y
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Test basic computation
    #[test]
    fn test_basic_computation() {
        // logB=4.6, D=5.0, C=30.0, y=0.01
        // => 4.6 - 5.0*0.01 + 30.0*0.0001/2 = 4.6 - 0.05 + 0.0015 = 4.5515
        let result = bond_log_price(4.6, 5.0, 30.0, 0.01);
        let expected = 4.6 - 0.05 + 0.0015;
        assert!((result - expected).abs() < EPS);
    }

    /// Lean: `bondLogPrice_at_zero_y` — at y=0 reduces to logB
    #[test]
    fn test_at_zero_yield() {
        let log_b = 4.605;
        let result = bond_log_price_at_zero_y(log_b, 7.0, 50.0);
        assert!((result - log_b).abs() < EPS);
    }

    /// Lean: `bondLogPrice_zero_convexity` — C=0 gives linear form
    #[test]
    fn test_zero_convexity() {
        let log_b = 4.6;
        let d = 5.0;
        let y = 0.02;
        let result = bond_log_price_zero_convexity(log_b, d, y);
        let expected = log_b - d * y;
        assert!((result - expected).abs() < EPS);
    }

    /// Lean: `bondLogPrice_linear_logB` — shift in logB propagates
    #[test]
    fn test_linear_logb() {
        let log_b = 4.6;
        let delta = 0.3;
        let d = 5.0;
        let c = 30.0;
        let y = 0.01;
        let base = bond_log_price(log_b, d, c, y);
        let shifted = bond_log_price_shifted(log_b, delta, d, c, y);
        assert!((shifted - (base + delta)).abs() < EPS);
    }

    /// Derivative at y=0 equals -D
    #[test]
    fn test_deriv_at_zero() {
        let d = 7.5;
        let c = 40.0;
        let deriv = bond_log_price_deriv(d, c, 0.0);
        assert!((deriv - (-d)).abs() < EPS);
    }

    /// Convexity contributes positively for y != 0 when C > 0
    #[test]
    fn test_convexity_positive_contribution() {
        let log_b = 4.6;
        let d = 5.0;
        let y = 0.02;
        let without_c = bond_log_price(log_b, d, 0.0, y);
        let with_c = bond_log_price(log_b, d, 50.0, y);
        assert!(with_c > without_c);
    }
}
