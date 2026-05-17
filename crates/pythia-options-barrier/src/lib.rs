//! # pythia-options-barrier
//!
//! Verified barrier option payoff bounds and identities.
//!
//! ## Lean specification (`Pythia.Finance.Options.BarrierOption`)
//!
//! - **Barrier dominance**: down-and-out call <= vanilla call (`downOut_le_vanilla`)
//! - **Knock-in/knock-out parity**: in + out = vanilla (`knock_in_out_parity`)
//! - **Barrier call non-negative** (`downOut_nonneg`)
//! - **Discrete >= continuous**: discrete monitoring >= continuous price (`discrete_ge_continuous`)
//! - **Up-and-out put at barrier**: payoff = 0 when S >= H (`upOut_put_itm_at_barrier`)
//! - **Rebate total non-negative** (`rebate_total_nonneg`)

/// Vanilla call payoff: max(S - K, 0).
///
/// # Lean: `vanillaCall`
#[inline(always)]
pub fn vanilla_call(s: f64, k: f64) -> f64 {
    (s - k).max(0.0)
}

/// Down-and-out call payoff: max(S - K, 0) if alive, else 0.
///
/// # Lean: `downOutCall`
#[inline(always)]
pub fn down_out_call(s: f64, k: f64, alive: bool) -> f64 {
    if alive { (s - k).max(0.0) } else { 0.0 }
}

/// Knock-in/knock-out parity: given payoff_in + payoff_out = vanilla,
/// returns payoff_in = vanilla - payoff_out.
///
/// # Lean: `knock_in_out_parity`
#[inline(always)]
pub fn knock_in_from_parity(payoff_vanilla: f64, payoff_out: f64) -> f64 {
    payoff_vanilla - payoff_out
}

/// Up-and-out put payoff: max(K - S, 0) if S < H, else 0.
///
/// # Lean: `upOut_put_itm_at_barrier`
#[inline(always)]
pub fn up_out_put(s: f64, k: f64, h: f64) -> f64 {
    if s >= h { 0.0 } else { (k - s).max(0.0) }
}

/// Total payoff with rebate: option_payoff + rebate.
///
/// # Lean: `rebate_total_nonneg`
#[inline(always)]
pub fn payoff_with_rebate(option_payoff: f64, rebate: f64) -> f64 {
    option_payoff + rebate
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn barrier_dominance() {
        // down-and-out call <= vanilla call for any alive flag
        for alive in [true, false] {
            assert!(down_out_call(110.0, 100.0, alive) <= vanilla_call(110.0, 100.0));
        }
    }

    #[test]
    fn knock_in_out_parity_holds() {
        let vanilla = vanilla_call(120.0, 100.0);
        let out = down_out_call(120.0, 100.0, true);
        let in_payoff = knock_in_from_parity(vanilla, out);
        assert!((in_payoff + out - vanilla).abs() < 1e-10);
    }

    #[test]
    fn down_out_nonneg() {
        assert!(down_out_call(90.0, 100.0, true) >= 0.0);
        assert!(down_out_call(110.0, 100.0, false) >= 0.0);
        assert!(down_out_call(110.0, 100.0, true) >= 0.0);
    }

    #[test]
    fn up_out_put_at_barrier() {
        // When S >= H, up-and-out put payoff is 0
        assert_eq!(up_out_put(150.0, 100.0, 130.0), 0.0);
        assert_eq!(up_out_put(130.0, 100.0, 130.0), 0.0);
    }

    #[test]
    fn rebate_total_nonneg() {
        assert!(payoff_with_rebate(5.0, 2.0) >= 0.0);
        assert!(payoff_with_rebate(0.0, 3.0) >= 0.0);
    }

    #[test]
    fn vanilla_call_otm_is_zero() {
        assert_eq!(vanilla_call(90.0, 100.0), 0.0);
    }
}
