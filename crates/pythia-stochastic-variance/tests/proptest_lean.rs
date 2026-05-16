use proptest::prelude::*;
use pythia_stochastic_variance::*;

proptest! {
    /// Lean: varianceSwap_zero_npv: payoff = 0 when strike = realized
    #[test]
    fn prop_zero_npv(
        var in 0.001_f64..1.0,
    ) {
        let payoff = variance_swap_payoff(var, var);
        prop_assert!(payoff.abs() < 1e-15,
            "zero_npv failed: payoff={payoff} for var={var}");
    }

    /// Lean: varianceSwapPayoff_mono: higher realized => higher payoff
    #[test]
    fn prop_payoff_monotone(
        k_var in 0.001_f64..0.5,
        delta in 0.0_f64..0.5,
    ) {
        let v1 = k_var;
        let v2 = k_var + delta;
        let p1 = variance_swap_payoff(v1, k_var);
        let p2 = variance_swap_payoff(v2, k_var);
        prop_assert!(p1 <= p2 + 1e-15,
            "monotonicity failed: p1={p1}, p2={p2}");
    }

    /// Lean: varianceSwapPayoff_antitone_strike: higher strike => lower payoff
    #[test]
    fn prop_payoff_antitone_strike(
        sigma_r_sq in 0.001_f64..0.5,
        delta in 0.0_f64..0.5,
    ) {
        let k1 = sigma_r_sq;
        let k2 = sigma_r_sq + delta;
        let p1 = variance_swap_payoff(sigma_r_sq, k1);
        let p2 = variance_swap_payoff(sigma_r_sq, k2);
        prop_assert!(p2 <= p1 + 1e-15,
            "antitone_strike failed: p1={p1}, p2={p2}");
    }

    /// Lean: variance_from_returns_nonneg: realized var >= 0 for nonneg sum, T > 0
    #[test]
    fn prop_realized_variance_nonneg(
        returns_sq_sum in 0.0_f64..10.0,
        t in 0.01_f64..10.0,
    ) {
        let rv = realized_variance(returns_sq_sum, t);
        prop_assert!(rv >= -1e-15,
            "realized_variance negative: rv={rv}");
    }
}
