//! # pythia-options-asian
//!
//! Asian option payoff bounds — verified via Lean proofs.
//!
//! ## Lean specification (`Pythia.Finance.Options.AsianOption`)
//!
//! - **Arith Asian call nonneg**: `0 <= max(avg - K, 0)` (`arith_asian_call_nonneg`)
//! - **Geom call <= arith call**: AM-GM dominance (`geom_call_le_arith_call`)
//! - **Floating-strike nonneg**: `0 <= max(S_T - avg, 0)` (`floating_strike_nonneg`)
//! - **Convex in avg**: higher avg => higher payoff (`asian_call_convex_in_avg`)

/// Arithmetic average of a price series.
/// # Lean: `arithmeticAvg`
#[inline(always)]
pub fn arithmetic_avg(prices: &[f64]) -> f64 {
    if prices.is_empty() {
        return 0.0;
    }
    prices.iter().sum::<f64>() / prices.len() as f64
}

/// Geometric average of a price series (via exp of mean log).
/// # Lean: `geometricAvg`
#[inline(always)]
pub fn geometric_avg(prices: &[f64]) -> f64 {
    if prices.is_empty() {
        return 0.0;
    }
    let mean_log = prices.iter().map(|s| s.ln()).sum::<f64>() / prices.len() as f64;
    mean_log.exp()
}

/// Fixed-strike Asian call payoff: max(avg - K, 0).
/// # Lean: `arith_asian_call_nonneg` (nonneg property)
#[inline(always)]
pub fn asian_call_payoff(avg: f64, k: f64) -> f64 {
    (avg - k).max(0.0)
}

/// Floating-strike Asian call payoff: max(S_T - avg, 0).
/// # Lean: `floating_strike_nonneg`
#[inline(always)]
pub fn floating_strike_payoff(s_t: f64, avg: f64) -> f64 {
    (s_t - avg).max(0.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arith_asian_call_nonneg() {
        assert!(asian_call_payoff(100.0, 105.0) >= 0.0);
        assert!(asian_call_payoff(110.0, 100.0) >= 0.0);
    }

    #[test]
    fn geom_call_le_arith_call() {
        let prices = vec![90.0, 100.0, 110.0, 120.0];
        let arith = arithmetic_avg(&prices);
        let geom = geometric_avg(&prices);
        // AM-GM: geometric <= arithmetic
        assert!(geom <= arith + 1e-10);
        // Therefore geom call payoff <= arith call payoff
        let k = 100.0;
        assert!(asian_call_payoff(geom, k) <= asian_call_payoff(arith, k) + 1e-10);
    }

    #[test]
    fn floating_strike_nonneg() {
        assert!(floating_strike_payoff(120.0, 100.0) >= 0.0);
        assert!(floating_strike_payoff(80.0, 100.0) >= 0.0);
    }

    #[test]
    fn convex_in_avg() {
        let k = 100.0;
        assert!(asian_call_payoff(95.0, k) <= asian_call_payoff(105.0, k));
    }

    #[test]
    fn arithmetic_avg_basic() {
        let prices = vec![100.0, 200.0];
        assert!((arithmetic_avg(&prices) - 150.0).abs() < 1e-10);
    }

    #[test]
    fn geometric_avg_basic() {
        let prices = vec![4.0, 9.0];
        // geometric avg = exp((ln4 + ln9)/2) = exp(ln6) = 6
        assert!((geometric_avg(&prices) - 6.0).abs() < 1e-10);
    }
}
