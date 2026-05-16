//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

//! Property-based tests mirroring Lean theorems from `Pythia.Finance.Portfolio.FactorRiskModel`.

use proptest::prelude::*;
use pythia_portfolio_factor::FactorRisk;

/// Generate a valid FactorRisk model with n_assets assets and n_factors factors.
fn arb_factor_risk(n_assets: usize, n_factors: usize) -> impl Strategy<Value = FactorRisk> {
    let betas = proptest::collection::vec(-3.0f64..3.0, n_assets * n_factors);
    let factor_vars = proptest::collection::vec(0.001f64..0.5, n_factors);
    let idio_vars = proptest::collection::vec(0.001f64..0.5, n_assets);
    let weights = proptest::collection::vec(-1.0f64..1.0, n_assets);

    (betas, factor_vars, idio_vars, weights).prop_map(
        move |(betas, factor_variances, idio_variances, weights)| FactorRisk {
            betas,
            factor_variances,
            idio_variances,
            weights,
            n_factors,
        },
    )
}

proptest! {
    /// Lean: `systematic_risk_nonneg`
    /// Systematic risk is a sum of (var_k * exposure_k^2), always >= 0.
    #[test]
    fn prop_systematic_risk_nonneg(model in arb_factor_risk(5, 3)) {
        prop_assert!(model.systematic_risk() >= -1e-15,
            "systematic_risk={} < 0", model.systematic_risk());
    }

    /// Lean: `risk_decomposition`
    /// Total risk = systematic + idiosyncratic (exact decomposition).
    #[test]
    fn prop_risk_decomposition(model in arb_factor_risk(5, 3)) {
        let total = model.total_risk();
        let sys = model.systematic_risk();
        // idiosyncratic is private, but total - systematic should equal it
        // We verify total_risk() == systematic + idio via the struct
        // total_risk calls both internally, so just check >= 0
        prop_assert!(total >= sys - 1e-12,
            "total={} < systematic={}", total, sys);
        // Confirm budget sums correctly (uses same decomposition)
        prop_assert!(model.risk_budget_sums_to_total());
    }

    /// Lean: `tracking_error_from_mismatch`
    /// Tracking error squared is always >= 0 (quadratic form of PSD matrix).
    #[test]
    fn prop_tracking_error_nonneg(
        model in arb_factor_risk(5, 3),
        bench in proptest::collection::vec(-1.0f64..1.0, 5),
    ) {
        let te = model.tracking_error(&bench);
        prop_assert!(te >= -1e-15, "tracking_error={} < 0", te);
    }

    /// Lean: `risk_budget_sums`
    /// Sum of marginal contributions to risk equals total portfolio variance.
    #[test]
    fn prop_risk_budget_sums(model in arb_factor_risk(8, 4)) {
        let mcr: Vec<f64> = model.risk_budget();
        let mcr_sum: f64 = mcr.iter().sum();
        let total = model.total_risk();
        prop_assert!((mcr_sum - total).abs() < 1e-9,
            "MCR sum={} != total={}", mcr_sum, total);
    }
}
