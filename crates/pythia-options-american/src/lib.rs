//! # pythia-options-american
//!
//! Verified American vs European option pricing bounds.
//!
//! ## Lean specification (`Pythia.Finance.Options.EarlyExercise`)
//!
//! - **American ≥ European** (`american_ge_european`)
//! - **Premium nonneg** (`early_exercise_premium_nonneg`)
//! - **No-div call: American = European** (`american_call_no_div_eq_european`)
//! - **American ≥ intrinsic** (`american_ge_intrinsic`)
//! - **Deep ITM put early exercise value** (`put_early_exercise_value`)

/// Early exercise premium: V_am - V_eu.
/// # Lean: `early_exercise_premium_nonneg`
pub fn early_exercise_premium(v_american: f64, v_european: f64) -> f64 {
    v_american - v_european
}

/// Check American ≥ European.
/// # Lean: `american_ge_european`
pub fn check_american_ge_european(v_am: f64, v_eu: f64) -> bool {
    v_am >= v_eu - 1e-12
}

/// Check American ≥ intrinsic.
/// # Lean: `american_ge_intrinsic`
pub fn check_american_ge_intrinsic(v_am: f64, intrinsic: f64) -> bool {
    v_am >= intrinsic - 1e-12
}

/// Early exercise value for deep ITM put: intrinsic - PV(intrinsic).
/// # Lean: `put_early_exercise_value`
pub fn put_early_exercise_value(intrinsic: f64, pv_intrinsic: f64) -> f64 {
    intrinsic - pv_intrinsic
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn premium_nonneg() {
        assert!(early_exercise_premium(5.5, 5.0) >= 0.0);
    }

    #[test]
    fn no_div_call_zero_premium() {
        assert!((early_exercise_premium(5.0, 5.0)).abs() < 1e-10);
    }

    #[test]
    fn american_ge_european() {
        assert!(check_american_ge_european(5.5, 5.0));
    }

    #[test]
    fn american_ge_intrinsic() {
        assert!(check_american_ge_intrinsic(5.0, 3.0));
    }

    #[test]
    fn deep_itm_put_exercise() {
        assert!(put_early_exercise_value(10.0, 9.5) > 0.0);
    }
}
