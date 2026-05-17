//! # pythia-options-lookback
//!
//! Verified lookback option payoff bounds and identities.
//!
//! ## Lean specification (`Pythia.Finance.Options.LookbackOption`)
//!
//! - **Lookback call non-negative**: `lookback_call_nonneg`
//! - **Lookback dominates vanilla**: `lookback_dominates_vanilla`
//! - **Lookback put non-negative**: `lookback_put_nonneg`
//! - **Lookback straddle = range**: `lookback_straddle`

/// Floating-strike lookback call payoff: S_T - path_min.
///
/// # Lean: `lookbackCallPayoff`
#[inline(always)]
pub fn lookback_call_payoff(s_t: f64, path_min: f64) -> f64 {
    s_t - path_min
}

/// Floating-strike lookback put payoff: path_max - S_T.
///
/// # Lean: `lookbackPutPayoff`
#[inline(always)]
pub fn lookback_put_payoff(path_max: f64, s_t: f64) -> f64 {
    path_max - s_t
}

/// Vanilla call payoff: max(S_T - K, 0).
#[inline(always)]
pub fn vanilla_call(s_t: f64, k: f64) -> f64 {
    (s_t - k).max(0.0)
}

/// Lookback straddle: call + put = path_max - path_min (the range).
///
/// # Lean: `lookback_straddle`
#[inline(always)]
pub fn lookback_straddle(s_t: f64, path_min: f64, path_max: f64) -> f64 {
    lookback_call_payoff(s_t, path_min) + lookback_put_payoff(path_max, s_t)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Lean: `lookback_call_nonneg` — call payoff >= 0 when path_min <= S_T
    #[test]
    fn test_call_nonneg() {
        assert!(lookback_call_payoff(110.0, 95.0) >= 0.0);
        assert!(lookback_call_payoff(100.0, 100.0) >= 0.0);
        assert!(lookback_call_payoff(50.0, 30.0) >= 0.0);
    }

    /// Lean: `lookback_dominates_vanilla` — lookback call >= vanilla call
    #[test]
    fn test_dominates_vanilla() {
        // With S_0 as strike for vanilla, path_min <= S_0
        let s_t = 120.0;
        let s_0 = 100.0;
        let path_min = 90.0;
        let lookback = lookback_call_payoff(s_t, path_min);
        let vanilla = vanilla_call(s_t, s_0);
        assert!(lookback >= vanilla);
    }

    /// Lean: `lookback_dominates_vanilla` — OTM vanilla still dominated
    #[test]
    fn test_dominates_vanilla_otm() {
        let s_t = 95.0;
        let s_0 = 100.0;
        let path_min = 85.0;
        let lookback = lookback_call_payoff(s_t, path_min);
        let vanilla = vanilla_call(s_t, s_0);
        assert!(lookback >= vanilla);
    }

    /// Lean: `lookback_put_nonneg` — put payoff >= 0 when S_T <= path_max
    #[test]
    fn test_put_nonneg() {
        assert!(lookback_put_payoff(130.0, 110.0) >= 0.0);
        assert!(lookback_put_payoff(100.0, 100.0) >= 0.0);
        assert!(lookback_put_payoff(200.0, 150.0) >= 0.0);
    }

    /// Lean: `lookback_straddle` — call + put = path_max - path_min
    #[test]
    fn test_straddle_equals_range() {
        let s_t = 105.0;
        let path_min = 90.0;
        let path_max = 130.0;
        let straddle = lookback_straddle(s_t, path_min, path_max);
        let range = path_max - path_min;
        assert!((straddle - range).abs() < EPS);
    }

    /// Edge case: path_min == path_max == S_T (flat path)
    #[test]
    fn test_flat_path() {
        let s = 100.0;
        assert!((lookback_call_payoff(s, s)).abs() < EPS);
        assert!((lookback_put_payoff(s, s)).abs() < EPS);
        assert!((lookback_straddle(s, s, s)).abs() < EPS);
    }
}
