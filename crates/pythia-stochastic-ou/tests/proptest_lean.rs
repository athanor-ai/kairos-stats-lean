//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_stochastic_ou::*;

proptest! {
    /// Lean: `ouTerminal_zero_time`
    #[test]
    fn zero_time(x0 in -100.0f64..100.0, mu in -50.0f64..50.0, theta in 0.1f64..5.0) {
        prop_assert!((ou_terminal(x0, mu, theta, 0.0, 0.0) - x0).abs() < 1e-10);
    }

    /// Lean: `ouTerminal_at_mean`
    #[test]
    fn at_mean_stays(mu in -50.0f64..50.0, theta in 0.1f64..5.0, t in 0.0f64..20.0) {
        prop_assert!((ou_terminal(mu, mu, theta, t, 0.0) - mu).abs() < 1e-8);
    }

    /// Lean: `ouTerminal_linear_noise`
    #[test]
    fn linear_noise(x0 in -100.0f64..100.0, mu in -50.0f64..50.0, theta in 0.1f64..5.0, t in 0.0f64..10.0, noise in -10.0f64..10.0) {
        let base = ou_terminal(x0, mu, theta, t, 0.0);
        let with_noise = ou_terminal(x0, mu, theta, t, noise);
        prop_assert!((with_noise - base - noise).abs() < 1e-10);
    }

    /// Mean reversion: for large t, result approaches mu
    #[test]
    fn mean_reverts(x0 in -100.0f64..100.0, mu in -50.0f64..50.0, theta in 0.5f64..5.0) {
        let x = ou_terminal(x0, mu, theta, 50.0, 0.0);
        prop_assert!((x - mu).abs() < 1e-4);
    }
}
