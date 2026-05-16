//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_risk_liquidity::*;

proptest! {
    /// Lean: `liquidity_cost_nonneg`
    #[test]
    fn cost_nonneg(half_spread in 0.0f64..10.0, qty in 0.0f64..1000.0) {
        prop_assert!(check_cost_nonneg(half_spread, qty));
    }

    /// Lean: `liquidity_cost_mono`
    #[test]
    fn cost_mono(half_spread in 0.0f64..10.0, q1 in 0.0f64..500.0, extra in 0.0f64..500.0) {
        prop_assert!(check_cost_mono(half_spread, q1, q1 + extra));
    }

    /// Lean: `lvar_ge_var`
    #[test]
    fn lvar_ge_var_prop(var in -1e6f64..1e6, liq_cost in 0.0f64..1e6) {
        prop_assert!(check_lvar_ge_var(var, liq_cost));
    }

    /// Lean: `lvar_mono_spread`
    #[test]
    fn lvar_mono_spread_prop(var in -1e6f64..1e6, qty in 0.0f64..1000.0, s1 in 0.0f64..5.0, extra in 0.0f64..5.0) {
        prop_assert!(check_lvar_mono_spread(var, qty, s1, s1 + extra));
    }
}
