//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_stochastic_heston::HestonParams;

proptest! {
    /// Lean: `mean_reversion_pull_down` — above theta → negative drift
    #[test]
    fn reversion_down(kappa in 0.1f64..5.0, theta in 0.01f64..0.1, excess in 0.01f64..0.5) {
        let p = HestonParams { kappa, theta, xi: 0.3 };
        prop_assert!(p.drift(theta + excess) < 0.0);
    }

    /// Lean: `mean_reversion_pull_up` — below theta → positive drift
    #[test]
    fn reversion_up(kappa in 0.1f64..5.0, theta in 0.05f64..0.2, deficit in 0.01f64..0.04) {
        let p = HestonParams { kappa, theta, xi: 0.3 };
        prop_assert!(p.drift(theta - deficit) > 0.0);
    }

    /// Lean: `equilibrium_zero_drift`
    #[test]
    fn equilibrium(kappa in 0.1f64..5.0, theta in 0.01f64..0.2) {
        let p = HestonParams { kappa, theta, xi: 0.3 };
        prop_assert!(p.drift(theta).abs() < 1e-12);
    }

    /// Lean: `reversion_speed_mono` — higher kappa → stronger pull
    #[test]
    fn speed_mono(k1 in 0.1f64..2.0, extra in 0.1f64..3.0, theta in 0.01f64..0.1, v in 0.05f64..0.2) {
        let p1 = HestonParams { kappa: k1, theta, xi: 0.3 };
        let p2 = HestonParams { kappa: k1 + extra, theta, xi: 0.3 };
        if v > theta {
            prop_assert!(p2.drift(v) <= p1.drift(v) + 1e-10);
        } else {
            prop_assert!(p2.drift(v) >= p1.drift(v) - 1e-10);
        }
    }
}
