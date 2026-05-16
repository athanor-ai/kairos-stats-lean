//! # Volatility Smile / Skew
//!
//! Rust port of `Pythia.Finance.Risk.VolatilitySmile`.
//!
//! The implied volatility smile is modelled as a quadratic in log-moneyness:
//!
//! ```text
//! vol(m) = sigma_atm + skew * m + smile * m^2
//! ```
//!
//! where `m = log(K/S)` is log-moneyness.
//!
//! ## Lean theorems mirrored
//!
//! - [`impliedVol`] — quadratic smile parametrisation
//! - [`impliedVol_atm`] — at `m = 0` implied vol equals `sigma_atm`
//! - [`impliedVol_symmetric_no_skew`] — symmetric when `skew = 0`
//! - [`impliedVol_quadratic_form`] — unfolds definition
//! - [`impliedVol_nonneg_sufficient`] — sufficient condition for non-negativity
//! - [`impliedVol_mono_smile`] — monotone in smile coefficient

/// Compute the quadratic implied-volatility smile:
/// `sigma_atm + skew * m + smile * m^2`.
///
/// Corresponds to Lean `Pythia.Finance.impliedVol`.
#[inline]
pub fn implied_vol(sigma_atm: f64, skew: f64, smile: f64, m: f64) -> f64 {
    sigma_atm + skew * m + smile * m * m
}

/// At zero moneyness the implied vol equals `sigma_atm`.
///
/// Corresponds to Lean `impliedVol_atm`.
#[inline]
pub fn implied_vol_atm(sigma_atm: f64, skew: f64, smile: f64) -> f64 {
    implied_vol(sigma_atm, skew, smile, 0.0)
}

/// Check smile symmetry when `skew = 0`:
/// `implied_vol(sigma_atm, 0, smile, m) == implied_vol(sigma_atm, 0, smile, -m)`.
///
/// Corresponds to Lean `impliedVol_symmetric_no_skew`.
#[inline]
pub fn implied_vol_is_symmetric_no_skew(sigma_atm: f64, smile: f64, m: f64) -> bool {
    let v_pos = implied_vol(sigma_atm, 0.0, smile, m);
    let v_neg = implied_vol(sigma_atm, 0.0, smile, -m);
    (v_pos - v_neg).abs() < 1e-14 * (1.0 + v_pos.abs())
}

/// Sufficient condition for non-negativity: checks that
/// `|skew * m| <= sigma_atm + smile * m^2`.
///
/// Corresponds to Lean `impliedVol_nonneg_sufficient`.
#[inline]
pub fn implied_vol_nonneg_check(sigma_atm: f64, skew: f64, smile: f64, m: f64) -> bool {
    if sigma_atm <= 0.0 || smile < 0.0 {
        return false;
    }
    (skew * m).abs() <= sigma_atm + smile * m * m
}

/// Checks monotonicity in smile coefficient: for any fixed `m != 0`,
/// if `smile1 <= smile2` then `implied_vol(..., smile1, m) <= implied_vol(..., smile2, m)`.
///
/// Corresponds to Lean `impliedVol_mono_smile`.
#[inline]
pub fn implied_vol_mono_smile(
    sigma_atm: f64,
    skew: f64,
    smile1: f64,
    smile2: f64,
    m: f64,
) -> bool {
    if smile1 > smile2 {
        return false; // precondition not met
    }
    implied_vol(sigma_atm, skew, smile1, m) <= implied_vol(sigma_atm, skew, smile2, m)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Basic computation: vol(0.20, 0.0, 0.0, 0.5) = 0.20
    #[test]
    fn test_flat_smile() {
        let v = implied_vol(0.20, 0.0, 0.0, 0.5);
        assert!((v - 0.20).abs() < EPS);
    }

    /// Lean: `impliedVol_atm` — at m=0, vol = sigma_atm
    #[test]
    fn test_atm_level() {
        let sigma_atm = 0.25;
        let v = implied_vol_atm(sigma_atm, -0.1, 0.05);
        assert!((v - sigma_atm).abs() < EPS);
    }

    /// Lean: `impliedVol_symmetric_no_skew` — symmetric when skew=0
    #[test]
    fn test_symmetry_no_skew() {
        assert!(implied_vol_is_symmetric_no_skew(0.20, 0.05, 0.3));
        assert!(implied_vol_is_symmetric_no_skew(0.20, 0.05, -0.3));
    }

    /// Lean: `impliedVol_quadratic_form` — definition check
    #[test]
    fn test_quadratic_form() {
        let sigma_atm = 0.20;
        let skew = -0.05;
        let smile = 0.02;
        let m = 0.3;
        let v = implied_vol(sigma_atm, skew, smile, m);
        let expected = sigma_atm + skew * m + smile * m * m;
        assert!((v - expected).abs() < EPS);
    }

    /// Lean: `impliedVol_nonneg_sufficient` — sufficient non-negativity
    #[test]
    fn test_nonneg_sufficient() {
        // sigma_atm=0.20, skew=-0.1, smile=0.05, m=0.5
        // |skew*m| = 0.05, sigma_atm + smile*m^2 = 0.20 + 0.0125 = 0.2125 >= 0.05
        assert!(implied_vol_nonneg_check(0.20, -0.1, 0.05, 0.5));
        let v = implied_vol(0.20, -0.1, 0.05, 0.5);
        assert!(v >= 0.0);
    }

    /// Lean: `impliedVol_mono_smile` — higher smile => higher vol away from ATM
    #[test]
    fn test_mono_smile() {
        let v1 = implied_vol(0.20, -0.05, 0.01, 0.5);
        let v2 = implied_vol(0.20, -0.05, 0.05, 0.5);
        assert!(v1 <= v2);
        assert!(implied_vol_mono_smile(0.20, -0.05, 0.01, 0.05, 0.5));
    }
}
