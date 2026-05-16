//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_portfolio_attribution::*;

proptest! {
    /// Lean: `bhb_exact` -- allocation + selection + interaction = w_p*r_p - w_b*r_b
    #[test]
    fn bhb_sums_to_active(
        w_p in 0.0f64..1.0,
        w_b in 0.0f64..1.0,
        r_p in -0.5f64..0.5,
        r_b in -0.5f64..0.5,
    ) {
        let (alloc, sel, inter) = bhb_decompose(w_p, w_b, r_p, r_b);
        let active = w_p * r_p - w_b * r_b;
        prop_assert!((alloc + sel + inter - active).abs() < 1e-10);
    }

    /// Lean: `geometric_link` -- (1+r1)(1+r2)-1 = r1 + r2 + r1*r2
    #[test]
    fn geometric_link_identity(r1 in -0.5f64..0.5, r2 in -0.5f64..0.5) {
        let geo = geometric_link(r1, r2);
        let expected = r1 + r2 + r1 * r2;
        prop_assert!((geo - expected).abs() < 1e-12);
    }

    /// Lean: `geometric_exceeds_arithmetic` -- geo > arith for positive returns
    #[test]
    fn geometric_exceeds_arithmetic(r1 in 0.001f64..0.5, r2 in 0.001f64..0.5) {
        prop_assert!(geometric_link(r1, r2) > arithmetic_link(r1, r2));
    }

    /// Lean: `currency_effect_additive` -- round-trip consistency
    #[test]
    fn currency_additive(r_local in -0.5f64..0.5, r_fx in -0.2f64..0.2) {
        let total = currency_adjusted_return(r_local, r_fx);
        prop_assert!((total - r_local - r_fx).abs() < 1e-15);
    }
}
