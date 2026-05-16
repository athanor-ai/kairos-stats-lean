//! Variance Swap Pricing
//!
//! Implements the algebraic kernel from:
//! Pythia/Finance/Stochastic/VarianceSwap.lean
//!
//! payoff = sigma_realized^2 - K_var
//! fair strike: K_var = (2/T) * E_Q[log(S_0/S_T)]

/// Variance swap payoff at expiry: realized variance minus strike.
pub fn variance_swap_payoff(sigma_realized_sq: f64, k_var: f64) -> f64 {
    sigma_realized_sq - k_var
}

/// Annualized realized variance from sum of squared returns.
///   realized_var = sum(r_i^2) / T
pub fn realized_variance(returns_sq_sum: f64, t: f64) -> f64 {
    returns_sq_sum / t
}

/// Fair variance swap strike (log-contract replication):
///   K_var = (2/T) * E_Q[log(S_0/S_T)]
pub fn fair_strike_log_contract(log_forward_ratio: f64, t: f64) -> f64 {
    (2.0 / t) * log_forward_ratio
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: varianceSwapPayoff_pos_iff: payoff > 0 iff realized > strike
    #[test]
    fn test_payoff_pos_iff() {
        let sigma_r_sq = 0.04; // 20% vol squared
        let k_var = 0.03;
        let payoff = variance_swap_payoff(sigma_r_sq, k_var);
        assert!(payoff > 0.0);
        assert!(k_var < sigma_r_sq);
    }

    /// Lean: varianceSwap_zero_npv: at fair strike, payoff = 0
    #[test]
    fn test_zero_npv() {
        let expected_var = 0.04;
        let payoff = variance_swap_payoff(expected_var, expected_var);
        assert!((payoff).abs() < 1e-15);
    }

    /// Lean: long_variance_profit: if realized > strike, long profits
    #[test]
    fn test_long_variance_profit() {
        let sigma_r_sq = 0.06;
        let k_var = 0.04;
        assert!(variance_swap_payoff(sigma_r_sq, k_var) > 0.0);
    }

    /// Lean: varianceSwapPayoff_mono: higher realized => higher payoff
    #[test]
    fn test_payoff_mono() {
        let k_var = 0.04;
        let v1 = 0.03;
        let v2 = 0.05;
        assert!(variance_swap_payoff(v1, k_var) <= variance_swap_payoff(v2, k_var));
    }

    /// Lean: varianceSwapPayoff_antitone_strike: higher strike => lower payoff
    #[test]
    fn test_payoff_antitone_strike() {
        let sigma_r_sq = 0.05;
        let k1 = 0.03;
        let k2 = 0.04;
        assert!(variance_swap_payoff(sigma_r_sq, k2) <= variance_swap_payoff(sigma_r_sq, k1));
    }

    /// Lean: variance_from_returns_nonneg: realized var >= 0 for nonneg inputs
    #[test]
    fn test_realized_variance_nonneg() {
        let returns_sq_sum = 0.01;
        let t = 1.0;
        assert!(realized_variance(returns_sq_sum, t) >= 0.0);
    }
}
