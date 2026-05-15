//! # pythia-options-exotic
//!
//! Model-free exotic option pricing bounds.
//!
//! ## Lean specification (`Pythia.Finance.Options.ExoticBounds`)
//!
//! - **Knock-in ≤ vanilla** (`knockin_le_vanilla`)
//! - **KI + KO = vanilla** (`knockin_knockout_parity`)
//! - **Asian ≤ vanilla** (Jensen's inequality) (`asian_le_vanilla`)
//! - **Lookback ≥ vanilla** (`lookback_ge_vanilla`)
//! - **Digital in [0,1]** (`digital_bounded`)
//! - **Straddle nonneg** (`straddle_nonneg`)

/// Validate knock-in ≤ vanilla.
/// # Lean: `knockin_le_vanilla`
pub fn check_knockin_bound(knockin: f64, vanilla: f64) -> bool {
    knockin <= vanilla + 1e-12
}

/// Validate KI + KO = vanilla parity.
/// # Lean: `knockin_knockout_parity`
pub fn check_barrier_parity(knockin: f64, knockout: f64, vanilla: f64, tol: f64) -> bool {
    (knockin + knockout - vanilla).abs() < tol
}

/// Validate Asian ≤ vanilla.
/// # Lean: `asian_le_vanilla`
pub fn check_asian_bound(asian: f64, vanilla: f64) -> bool {
    asian <= vanilla + 1e-12
}

/// Validate lookback ≥ vanilla.
/// # Lean: `lookback_ge_vanilla`
pub fn check_lookback_bound(lookback: f64, vanilla: f64) -> bool {
    lookback >= vanilla - 1e-12
}

/// Validate digital option in [0, 1].
/// # Lean: `digital_bounded`
pub fn check_digital_bounded(price: f64) -> bool {
    price >= -1e-12 && price <= 1.0 + 1e-12
}

/// Validate spread in [0, strike_diff * discount].
/// # Lean: `spread_bounded`
pub fn check_spread_bounded(spread_val: f64, max_val: f64) -> bool {
    spread_val >= -1e-12 && spread_val <= max_val + 1e-12
}

/// Straddle value = call + put. Always nonneg.
/// # Lean: `straddle_nonneg`
pub fn straddle_value(call: f64, put: f64) -> f64 {
    call + put
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn knockin_bound() { assert!(check_knockin_bound(3.0, 5.0)); }

    #[test]
    fn barrier_parity() { assert!(check_barrier_parity(3.0, 2.0, 5.0, 1e-10)); }

    #[test]
    fn asian_bound() { assert!(check_asian_bound(4.0, 5.0)); }

    #[test]
    fn lookback_bound() { assert!(check_lookback_bound(7.0, 5.0)); }

    #[test]
    fn digital_valid() { assert!(check_digital_bounded(0.6)); assert!(!check_digital_bounded(1.5)); }

    #[test]
    fn straddle_nonneg() { assert!(straddle_value(3.0, 2.0) >= 0.0); }

    #[test]
    fn spread_valid() { assert!(check_spread_bounded(3.0, 5.0)); }
}
