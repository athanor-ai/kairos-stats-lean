//! # Calmar Ratio (algebraic form)
//!
//! Rust port of `Pythia.Finance.Portfolio.CalmarRatio`.
//!
//! The Calmar ratio measures risk-adjusted return using the maximum
//! drawdown as the risk denominator:
//!
//! ```text
//! Calmar(R, MDD_abs) = R / MDD_abs
//! ```
//!
//! where `R` is the annualised return and `MDD_abs > 0` is the absolute
//! magnitude of the maximum drawdown.
//!
//! ## Lean theorems mirrored
//!
//! - [`calmarRatio`] — definition `R / MDD_abs`
//! - [`calmarRatio_pos`] — positive when `R > 0` and `MDD_abs > 0`
//! - [`calmarRatio_nonneg`] — non-negative when `R >= 0` and `MDD_abs > 0`
//! - [`calmarRatio_mono_return`] — monotone in return
//! - [`calmarRatio_antitone_mdd`] — antitone in max drawdown

/// Compute the Calmar ratio: `R / MDD_abs`.
///
/// Corresponds to Lean `Pythia.Finance.calmarRatio`.
///
/// `MDD_abs` is the absolute magnitude of the maximum drawdown.
/// Returns `f64::NAN` when `MDD_abs == 0.0` per IEEE 754.
#[inline]
pub fn calmar_ratio(r: f64, mdd_abs: f64) -> f64 {
    r / mdd_abs
}

/// Returns `true` when the Calmar ratio is strictly positive.
///
/// Corresponds to Lean `calmarRatio_pos`: requires `R > 0` and `MDD_abs > 0`.
#[inline]
pub fn calmar_ratio_is_positive(r: f64, mdd_abs: f64) -> bool {
    r > 0.0 && mdd_abs > 0.0
}

/// Returns `true` when the Calmar ratio is non-negative.
///
/// Corresponds to Lean `calmarRatio_nonneg`: requires `R >= 0` and `MDD_abs > 0`.
#[inline]
pub fn calmar_ratio_is_nonneg(r: f64, mdd_abs: f64) -> bool {
    r >= 0.0 && mdd_abs > 0.0
}

/// Checks monotonicity in return: for fixed `MDD_abs > 0`,
/// if `R1 <= R2` then `calmar(R1) <= calmar(R2)`.
///
/// Corresponds to Lean `calmarRatio_mono_return`.
#[inline]
pub fn calmar_ratio_mono_return(r1: f64, r2: f64, mdd_abs: f64) -> bool {
    if mdd_abs <= 0.0 {
        return false; // precondition not met
    }
    if r1 <= r2 {
        calmar_ratio(r1, mdd_abs) <= calmar_ratio(r2, mdd_abs)
    } else {
        false
    }
}

/// Checks antitonicity in max drawdown: for fixed `R >= 0` and
/// `0 < M1 <= M2`, `calmar(R, M2) <= calmar(R, M1)`.
///
/// Corresponds to Lean `calmarRatio_antitone_mdd`.
#[inline]
pub fn calmar_ratio_antitone_mdd(r: f64, m1: f64, m2: f64) -> bool {
    if r < 0.0 || m1 <= 0.0 || m1 > m2 {
        return false; // preconditions not met
    }
    calmar_ratio(r, m2) <= calmar_ratio(r, m1)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Basic computation: Calmar(0.15, 0.30) = 0.5
    #[test]
    fn test_basic_computation() {
        let result = calmar_ratio(0.15, 0.30);
        assert!((result - 0.5).abs() < EPS);
    }

    /// Lean: `calmarRatio_pos` — positive when R > 0 and MDD_abs > 0
    #[test]
    fn test_positivity() {
        let cr = calmar_ratio(0.20, 0.10);
        assert!(cr > 0.0);
        assert!(calmar_ratio_is_positive(0.20, 0.10));
    }

    /// Lean: `calmarRatio_nonneg` — non-negative when R >= 0
    #[test]
    fn test_nonneg_zero_return() {
        let cr = calmar_ratio(0.0, 0.15);
        assert!(cr >= 0.0);
        assert!(calmar_ratio_is_nonneg(0.0, 0.15));
    }

    /// Lean: `calmarRatio_mono_return` — monotone in return
    #[test]
    fn test_monotone_return() {
        let mdd = 0.25;
        let cr1 = calmar_ratio(0.10, mdd);
        let cr2 = calmar_ratio(0.20, mdd);
        assert!(cr1 <= cr2);
        assert!(calmar_ratio_mono_return(0.10, 0.20, mdd));
    }

    /// Lean: `calmarRatio_antitone_mdd` — antitone in drawdown
    #[test]
    fn test_antitone_mdd() {
        let r = 0.15;
        let cr_small_dd = calmar_ratio(r, 0.10);
        let cr_large_dd = calmar_ratio(r, 0.30);
        assert!(cr_large_dd <= cr_small_dd);
        assert!(calmar_ratio_antitone_mdd(r, 0.10, 0.30));
    }

    /// Negative return yields negative ratio
    #[test]
    fn test_negative_return() {
        let cr = calmar_ratio(-0.05, 0.20);
        assert!(cr < 0.0);
        assert!(!calmar_ratio_is_positive(-0.05, 0.20));
    }
}
