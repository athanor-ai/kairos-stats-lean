//! # pythia-options-call-bounds
//!
//! European option price bounds — verified via Lean proofs.
//!
//! ## Lean specification (`Pythia.Finance.Options.CallPriceBounds`)
//!
//! - **Call payoff nonneg**: `0 <= max(S-K,0) * exp(-rT)` (`callPayoff_nonneg`)
//! - **Put payoff nonneg**: `0 <= max(K-S,0) * exp(-rT)` (`putPayoff_nonneg`)
//! - **Call dominates discounted intrinsic minus put** (`call_ge_intrinsic_discounted`)

/// Discounted call payoff: max(S - K, 0) * exp(-r*T).
/// # Lean: `callPayoff`
#[inline(always)]
pub fn call_payoff(s: f64, k: f64, t: f64, r: f64) -> f64 {
    (s - k).max(0.0) * (-r * t).exp()
}

/// Discounted put payoff: max(K - S, 0) * exp(-r*T).
/// # Lean: `putPayoff`
#[inline(always)]
pub fn put_payoff(s: f64, k: f64, t: f64, r: f64) -> f64 {
    (k - s).max(0.0) * (-r * t).exp()
}

/// Put-call parity (discounted): callPayoff - putPayoff = (S-K)*exp(-rT).
/// # Lean: `put_call_parity_discounted`
#[inline(always)]
pub fn parity_residual(s: f64, k: f64, t: f64, r: f64) -> f64 {
    call_payoff(s, k, t, r) - put_payoff(s, k, t, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn call_payoff_nonneg() {
        assert!(call_payoff(80.0, 100.0, 1.0, 0.05) >= 0.0);
        assert!(call_payoff(120.0, 100.0, 1.0, 0.05) >= 0.0);
    }

    #[test]
    fn put_payoff_nonneg() {
        assert!(put_payoff(80.0, 100.0, 1.0, 0.05) >= 0.0);
        assert!(put_payoff(120.0, 100.0, 1.0, 0.05) >= 0.0);
    }

    #[test]
    fn call_ge_intrinsic_discounted() {
        let s: f64 = 110.0;
        let k: f64 = 100.0;
        let t: f64 = 1.0;
        let r: f64 = 0.05;
        let lhs = (s - k) * (-r * t).exp() - put_payoff(s, k, t, r);
        let rhs = call_payoff(s, k, t, r);
        assert!(lhs <= rhs + 1e-10);
    }

    #[test]
    fn parity_identity() {
        let s = 105.0;
        let k = 100.0;
        let t = 0.5;
        let r = 0.03;
        let diff = parity_residual(s, k, t, r);
        let expected = (s - k) * (-r * t).exp();
        assert!((diff - expected).abs() < 1e-10);
    }

    #[test]
    fn call_payoff_deep_otm_zero() {
        // S << K => call payoff = 0
        let c = call_payoff(50.0, 100.0, 1.0, 0.05);
        assert!(c.abs() < 1e-10);
    }

    #[test]
    fn put_payoff_deep_otm_zero() {
        // S >> K => put payoff = 0
        let p = put_payoff(150.0, 100.0, 1.0, 0.05);
        assert!(p.abs() < 1e-10);
    }
}
