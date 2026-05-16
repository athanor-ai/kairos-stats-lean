//! # Information Ratio (algebraic form)
//!
//! Rust port of `Pythia.Finance.Portfolio.InformationRatio`.
//!
//! The Information ratio is the active-return Sharpe ratio relative to
//! a benchmark:
//!
//! ```text
//! IR(R_p, R_b, sigma_a) = (R_p - R_b) / sigma_a
//! ```
//!
//! where `R_p` is the portfolio return, `R_b` is the benchmark return,
//! and `sigma_a` is the tracking error (volatility of active return).
//!
//! ## Lean theorems mirrored
//!
//! - [`informationRatio`] — definition `(R_p - R_b) / sigma_a`
//! - [`informationRatio_pos`] — positive when `R_b < R_p` and `0 < sigma_a`
//! - [`informationRatio_diff_eq_active`] — `IR(R_p) - IR(R_q) = (R_p - R_q) / sigma_a`
//! - [`informationRatio_scale_invariant`] — invariant under positive rescaling

/// Compute the Information ratio: `(R_p - R_b) / sigma_a`.
///
/// Corresponds to Lean `Pythia.Finance.informationRatio`.
///
/// Returns `f64::NAN` when `sigma_a == 0.0`, per IEEE 754.
#[inline]
pub fn information_ratio(r_p: f64, r_b: f64, sigma_a: f64) -> f64 {
    (r_p - r_b) / sigma_a
}

/// Returns `true` when the Information ratio is strictly positive.
///
/// Corresponds to Lean `informationRatio_pos`: requires `R_b < R_p` and `0 < sigma_a`.
#[inline]
pub fn information_ratio_is_positive(r_p: f64, r_b: f64, sigma_a: f64) -> bool {
    r_b < r_p && sigma_a > 0.0
}

/// Structural identity: difference of two Information ratios at the same
/// benchmark and tracking error equals the active-return difference divided
/// by the tracking error.
///
/// `IR(R_p, R_b, sigma_a) - IR(R_q, R_b, sigma_a) = (R_p - R_q) / sigma_a`
///
/// Corresponds to Lean `informationRatio_diff_eq_active`.
#[inline]
pub fn information_ratio_diff(r_p: f64, r_q: f64, r_b: f64, sigma_a: f64) -> (f64, f64) {
    let diff_ir = information_ratio(r_p, r_b, sigma_a)
        - information_ratio(r_q, r_b, sigma_a);
    let expected = (r_p - r_q) / sigma_a;
    (diff_ir, expected)
}

/// Scale-invariance: `IR(alpha*R_p, alpha*R_b, alpha*sigma_a) == IR(R_p, R_b, sigma_a)`
/// for `alpha > 0`.
///
/// Corresponds to Lean `informationRatio_scale_invariant`.
#[inline]
pub fn information_ratio_scaled(alpha: f64, r_p: f64, r_b: f64, sigma_a: f64) -> f64 {
    information_ratio(alpha * r_p, alpha * r_b, alpha * sigma_a)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Test basic computation: IR(0.12, 0.08, 0.05) = 0.04/0.05 = 0.8
    #[test]
    fn test_basic_computation() {
        let result = information_ratio(0.12, 0.08, 0.05);
        let expected = 0.04 / 0.05;
        assert!((result - expected).abs() < EPS);
    }

    /// Lean: `informationRatio_pos` — positive when R_b < R_p and sigma_a > 0
    #[test]
    fn test_positivity() {
        let r = information_ratio(0.15, 0.10, 0.06);
        assert!(r > 0.0);
        assert!(information_ratio_is_positive(0.15, 0.10, 0.06));
    }

    /// Lean: `informationRatio_pos` — negative when R_p < R_b
    #[test]
    fn test_negative_active_return() {
        let r = information_ratio(0.05, 0.10, 0.06);
        assert!(r < 0.0);
        assert!(!information_ratio_is_positive(0.05, 0.10, 0.06));
    }

    /// Lean: `informationRatio_diff_eq_active`
    #[test]
    fn test_diff_eq_active() {
        let (diff_ir, expected) = information_ratio_diff(0.15, 0.10, 0.08, 0.04);
        assert!((diff_ir - expected).abs() < EPS);
    }

    /// Lean: `informationRatio_scale_invariant`
    #[test]
    fn test_scale_invariance() {
        let base = information_ratio(0.12, 0.08, 0.05);
        let scaled = information_ratio_scaled(2.5, 0.12, 0.08, 0.05);
        assert!((base - scaled).abs() < EPS);
    }

    /// Zero active return gives zero IR
    #[test]
    fn test_zero_active_return() {
        let r = information_ratio(0.10, 0.10, 0.05);
        assert!(r.abs() < EPS);
    }
}
