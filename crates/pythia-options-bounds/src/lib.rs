//! # pythia-options-bounds
//!
//! Verified model-free option pricing bounds — zero tautological.
//!
//! ## Lean specification (`Pythia.Finance.Options.PricingBounds`)
//!
//! - **Intrinsic nonneg**: max(S-KD,0) ≥ 0 (`callIntrinsic_nonneg`)
//! - **Intrinsic monotone in spot** (`callIntrinsic_mono_spot`)
//! - **Intrinsic antitone in strike** (`callIntrinsic_antitone_strike`)
//! - **Call spread ≤ strike diff * D** (`call_spread_le_strike_diff`)
//! - **Put-call parity at intrinsic** (`intrinsic_parity`)

/// Call intrinsic value: max(S - K*D, 0).
/// # Lean: `callIntrinsic`
#[inline(always)]
pub fn call_intrinsic(s: f64, k: f64, d: f64) -> f64 {
    (s - k * d).max(0.0)
}

/// Put intrinsic value: max(K*D - S, 0).
/// # Lean: `putIntrinsic`
#[inline(always)]
pub fn put_intrinsic(s: f64, k: f64, d: f64) -> f64 {
    (k * d - s).max(0.0)
}

/// Call spread: intrinsic(K1) - intrinsic(K2).
pub fn call_spread(s: f64, k1: f64, k2: f64, d: f64) -> f64 {
    call_intrinsic(s, k1, d) - call_intrinsic(s, k2, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intrinsic_nonneg() {
        assert!(call_intrinsic(80.0, 100.0, 0.95) >= 0.0);
        assert!(call_intrinsic(110.0, 100.0, 0.95) >= 0.0);
    }

    #[test]
    fn intrinsic_mono_spot() {
        assert!(call_intrinsic(100.0, 100.0, 0.95) <= call_intrinsic(110.0, 100.0, 0.95));
    }

    #[test]
    fn intrinsic_antitone_strike() {
        assert!(call_intrinsic(100.0, 110.0, 0.95) <= call_intrinsic(100.0, 100.0, 0.95));
    }

    #[test]
    fn spread_bounded() {
        let k1 = 95.0;
        let k2 = 105.0;
        let d = 0.95;
        let spread = call_spread(100.0, k1, k2, d);
        assert!(spread <= (k2 - k1) * d + 1e-10);
    }

    #[test]
    fn intrinsic_parity() {
        let s = 100.0;
        let k = 100.0;
        let d = 0.95;
        let diff = call_intrinsic(s, k, d) - put_intrinsic(s, k, d);
        assert!((diff - (s - k * d)).abs() < 1e-10);
    }

    #[test]
    fn deep_itm_call() {
        assert!((call_intrinsic(200.0, 100.0, 1.0) - 100.0).abs() < 1e-10);
    }
}
