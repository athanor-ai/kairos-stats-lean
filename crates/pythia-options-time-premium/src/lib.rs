//! # pythia-options-time-premium
//!
//! Option time premium (extrinsic value) — verified via Lean proofs.
//!
//! ## Lean specification (`Pythia.Finance.Options.OptionTimePremium`)
//!
//! - **Intrinsic nonneg**: `0 <= max(S - K, 0)` (`intrinsicValue_nonneg`)
//! - **Intrinsic zero OTM**: `S <= K => intrinsicValue = 0` (`intrinsicValue_zero_otm`)
//! - **Intrinsic ITM**: `K <= S => intrinsicValue = S - K` (`intrinsicValue_itm`)
//! - **Intrinsic mono spot**: `S1 <= S2 => intrinsic(S1) <= intrinsic(S2)` (`intrinsicValue_mono_spot`)
//! - **Time premium nonneg**: price >= intrinsic => premium >= 0 (`timePremium_nonneg_of_price_ge_intrinsic`)
//! - **Time premium = price OTM**: `S <= K => timePremium = C` (`timePremium_eq_price_otm`)

/// Intrinsic value of a European call: max(S - K, 0).
/// # Lean: `intrinsicValue`
#[inline(always)]
pub fn intrinsic_value(s: f64, k: f64) -> f64 {
    (s - k).max(0.0)
}

/// Time premium (extrinsic value): C - intrinsicValue(S, K).
/// # Lean: `timePremium`
#[inline(always)]
pub fn time_premium(c: f64, s: f64, k: f64) -> f64 {
    c - intrinsic_value(s, k)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intrinsic_nonneg() {
        assert!(intrinsic_value(80.0, 100.0) >= 0.0);
        assert!(intrinsic_value(120.0, 100.0) >= 0.0);
    }

    #[test]
    fn intrinsic_zero_otm() {
        assert!((intrinsic_value(90.0, 100.0) - 0.0).abs() < 1e-10);
        assert!((intrinsic_value(100.0, 100.0) - 0.0).abs() < 1e-10);
    }

    #[test]
    fn intrinsic_itm() {
        assert!((intrinsic_value(120.0, 100.0) - 20.0).abs() < 1e-10);
    }

    #[test]
    fn intrinsic_mono_spot() {
        assert!(intrinsic_value(90.0, 100.0) <= intrinsic_value(110.0, 100.0));
    }

    #[test]
    fn time_premium_nonneg() {
        // C = 15, S = 110, K = 100 => intrinsic = 10, premium = 5
        assert!(time_premium(15.0, 110.0, 100.0) >= 0.0);
    }

    #[test]
    fn time_premium_eq_price_otm() {
        // OTM: S <= K, intrinsic = 0, so premium = C
        let c = 5.0;
        assert!((time_premium(c, 90.0, 100.0) - c).abs() < 1e-10);
    }
}
