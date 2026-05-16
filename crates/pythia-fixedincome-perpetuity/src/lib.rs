//! # Perpetuity Present Value
//!
//! Rust port of `Pythia.Finance.FixedIncome.Perpetuity`.
//!
//! A perpetuity paying a constant cashflow `C` per period under discount
//! rate `r > 0` has present value:
//!
//! ```text
//! PV(C, r) = C / r
//! ```
//!
//! This is the classical Gordon-growth limit (with growth rate zero).
//!
//! ## Lean theorems mirrored
//!
//! - [`perpetuityValue`] — definition `C / r`
//! - [`perpetuityValue_pos`] — positive when `C > 0` and `r > 0`
//! - [`perpetuityValue_nonneg`] — non-negative when `C >= 0` and `r > 0`
//! - [`perpetuityValue_antitone_rate`] — antitone in `r` for `C >= 0`

/// Compute the present value of a perpetuity: `C / r`.
///
/// Corresponds to Lean `Pythia.Finance.perpetuityValue`.
///
/// Returns `f64::INFINITY` when `r == 0.0` per IEEE 754.
#[inline]
pub fn perpetuity_value(c: f64, r: f64) -> f64 {
    c / r
}

/// Returns `true` when the perpetuity value is strictly positive.
///
/// Corresponds to Lean `perpetuityValue_pos`: requires `C > 0` and `r > 0`.
#[inline]
pub fn perpetuity_value_is_positive(c: f64, r: f64) -> bool {
    c > 0.0 && r > 0.0
}

/// Returns `true` when the perpetuity value is non-negative.
///
/// Corresponds to Lean `perpetuityValue_nonneg`: requires `C >= 0` and `r > 0`.
#[inline]
pub fn perpetuity_value_is_nonneg(c: f64, r: f64) -> bool {
    c >= 0.0 && r > 0.0
}

/// Checks antitonicity in rate: for fixed `C >= 0` and `0 < r1 <= r2`,
/// `perpetuity_value(C, r2) <= perpetuity_value(C, r1)`.
///
/// Corresponds to Lean `perpetuityValue_antitone_rate`.
#[inline]
pub fn perpetuity_value_antitone_rate(c: f64, r1: f64, r2: f64) -> bool {
    if c < 0.0 || r1 <= 0.0 || r1 > r2 {
        return false; // preconditions not met
    }
    perpetuity_value(c, r2) <= perpetuity_value(c, r1)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Basic computation: PV(100, 0.05) = 2000
    #[test]
    fn test_basic_computation() {
        let result = perpetuity_value(100.0, 0.05);
        assert!((result - 2000.0).abs() < EPS);
    }

    /// Lean: `perpetuityValue_pos` — positive when C > 0 and r > 0
    #[test]
    fn test_positivity() {
        let pv = perpetuity_value(50.0, 0.08);
        assert!(pv > 0.0);
        assert!(perpetuity_value_is_positive(50.0, 0.08));
    }

    /// Lean: `perpetuityValue_nonneg` — non-negative when C >= 0 and r > 0
    #[test]
    fn test_nonneg_zero_cashflow() {
        let pv = perpetuity_value(0.0, 0.10);
        assert!(pv >= 0.0);
        assert!(perpetuity_value_is_nonneg(0.0, 0.10));
    }

    /// Lean: `perpetuityValue_antitone_rate` — lower rate gives higher PV
    #[test]
    fn test_antitone_rate() {
        let pv_low = perpetuity_value(100.0, 0.03);
        let pv_high = perpetuity_value(100.0, 0.08);
        assert!(pv_high <= pv_low);
        assert!(perpetuity_value_antitone_rate(100.0, 0.03, 0.08));
    }

    /// Negative cashflow gives negative PV (not formally proved but sanity)
    #[test]
    fn test_negative_cashflow() {
        let pv = perpetuity_value(-50.0, 0.05);
        assert!(pv < 0.0);
        assert!(!perpetuity_value_is_positive(-50.0, 0.05));
    }

    /// Gordon growth identity: PV = C/r for known pair
    #[test]
    fn test_gordon_identity() {
        let c = 7.5;
        let r = 0.125;
        let pv = perpetuity_value(c, r);
        assert!((pv - 60.0).abs() < EPS);
    }
}
