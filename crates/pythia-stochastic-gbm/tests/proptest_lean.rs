//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_stochastic_gbm::*;

proptest! {
    /// Lean: `gbmTerminal_pos` — GBM always positive for S0 > 0
    #[test]
    fn gbm_positive(s0 in 0.01f64..10000.0, mu in -0.5f64..0.5, sigma in 0.01f64..1.0, t in 0.01f64..10.0, w in -5.0f64..5.0) {
        prop_assert!(gbm_terminal(s0, mu, sigma, t, w) > 0.0);
    }

    /// Lean: `gbmTerminal_mono_drift` — higher drift → higher terminal
    #[test]
    fn drift_monotone(s0 in 1.0f64..1000.0, mu1 in -0.3f64..0.2, extra in 0.0f64..0.3, sigma in 0.01f64..0.5, t in 0.1f64..5.0, w in -3.0f64..3.0) {
        let mu2 = mu1 + extra;
        prop_assert!(gbm_terminal(s0, mu1, sigma, t, w) <= gbm_terminal(s0, mu2, sigma, t, w) + 1e-10);
    }

    /// Lean: `vol_drag_nonneg`
    #[test]
    fn vol_drag_nonneg_prop(sigma in -2.0f64..2.0) {
        prop_assert!(vol_drag(sigma) >= 0.0);
    }

    /// Lean: `log_return_decompose`
    #[test]
    fn log_return_matches(s0 in 1.0f64..1000.0, mu in -0.5f64..0.5, sigma in 0.01f64..1.0, t in 0.01f64..5.0, w in -3.0f64..3.0) {
        let s_t = gbm_terminal(s0, mu, sigma, t, w);
        let lr_price = (s_t / s0).ln();
        let lr_formula = log_return(s0, mu, sigma, t, w);
        prop_assert!((lr_price - lr_formula).abs() < 1e-8);
    }
}
