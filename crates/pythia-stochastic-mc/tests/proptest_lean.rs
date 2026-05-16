//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_stochastic_mc::*;

proptest! {
    /// Lean: `mc_se_nonneg`
    #[test]
    fn se_nonneg(sigma in 0.0f64..1.0, n in 1usize..100000) {
        prop_assert!(mc_se(sigma, n) >= 0.0);
    }

    /// Lean: `mc_se_antitone` — more samples → lower SE
    #[test]
    fn se_antitone(sigma in 0.01f64..1.0, n1 in 1usize..10000, extra in 1usize..10000) {
        prop_assert!(mc_se(sigma, n1 + extra) <= mc_se(sigma, n1) + 1e-12);
    }

    /// Lean: `ci_width_nonneg`
    #[test]
    fn ci_nonneg(z in 0.0f64..3.0, se in 0.0f64..1.0) {
        prop_assert!(ci_width(z, se) >= 0.0);
    }

    /// Lean: `variance_reduction`
    #[test]
    fn reduction_helps(sigma in 0.1f64..1.0, reduction in 0.01f64..0.5, n in 1usize..10000) {
        let reduced = sigma - reduction;
        if reduced > 0.0 {
            prop_assert!(mc_se_reduced(reduced, n) <= mc_se(sigma, n) + 1e-12);
        }
    }
}
