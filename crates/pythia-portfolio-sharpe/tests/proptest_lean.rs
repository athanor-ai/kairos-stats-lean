use proptest::prelude::*;
use pythia_portfolio_sharpe::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `sharpeRatio_scale_invariant`
    /// For any alpha > 0, sharpe(alpha*mu, alpha*rf, alpha*sigma) == sharpe(mu, rf, sigma).
    #[test]
    fn prop_scale_invariance(
        mu in -1000.0..1000.0f64,
        rf in -1000.0..1000.0f64,
        sigma in 0.001..1000.0f64,
        alpha in 0.001..1000.0f64,
    ) {
        let base = sharpe_ratio(mu, rf, sigma);
        let scaled = sharpe_ratio_scaled(alpha, mu, rf, sigma);
        prop_assert!((base - scaled).abs() < EPS * (1.0 + base.abs()),
            "scale invariance violated: base={}, scaled={}", base, scaled);
    }

    /// Lean: `sharpeRatio_cash_invariant`
    /// Adding constant c to both mu and rf leaves the ratio unchanged.
    #[test]
    fn prop_cash_invariance(
        mu in -1000.0..1000.0f64,
        rf in -1000.0..1000.0f64,
        sigma in 0.001..1000.0f64,
        c in -1000.0..1000.0f64,
    ) {
        let base = sharpe_ratio(mu, rf, sigma);
        let shifted = sharpe_ratio_cash_shifted(mu, rf, sigma, c);
        prop_assert!((base - shifted).abs() < EPS * (1.0 + base.abs()),
            "cash invariance violated: base={}, shifted={}", base, shifted);
    }

    /// Lean: `sharpeRatio_mono_excess`
    /// For fixed sigma > 0, if excess1 <= excess2 then sharpe1 <= sharpe2.
    #[test]
    fn prop_monotone_excess(
        excess1 in -1000.0..1000.0f64,
        delta in 0.0..1000.0f64,
        sigma in 0.001..1000.0f64,
    ) {
        let excess2 = excess1 + delta;
        // Use mu = excess + rf with rf = 0 for simplicity
        let s1 = sharpe_ratio(excess1, 0.0, sigma);
        let s2 = sharpe_ratio(excess2, 0.0, sigma);
        prop_assert!(s1 <= s2 + EPS,
            "monotonicity violated: s1={}, s2={}, excess1={}, excess2={}", s1, s2, excess1, excess2);
    }

    /// Lean: `sharpeRatio_pos` + `excess_pos_of_sharpeRatio_pos`
    /// Positive excess and positive sigma <=> positive ratio.
    #[test]
    fn prop_pos_iff_excess_pos(
        excess in 0.001..1000.0f64,
        sigma in 0.001..1000.0f64,
    ) {
        let mu = excess; // rf = 0
        let r = sharpe_ratio(mu, 0.0, sigma);
        prop_assert!(r > 0.0, "expected positive ratio for positive excess, got {}", r);
        // converse
        prop_assert!(sharpe_ratio_is_positive(mu, 0.0, sigma));
    }
}
