//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

//! Property tests for delta hedging, mirroring Lean spec `Pythia.Finance.DeltaHedging`.

use proptest::prelude::*;
use pythia_options_hedging::{DeltaHedge, vol_arb_pnl};

proptest! {
    /// Lean: `gammaPnL_nonneg` — long gamma (gamma >= 0) always yields non-negative gamma P&L.
    #[test]
    fn prop_gamma_pnl_nonneg(
        gamma in 0.0f64..10.0,
        ds in -100.0f64..100.0,
    ) {
        let h = DeltaHedge::new(0.5, gamma, -0.01);
        prop_assert!(h.gamma_pnl(ds) >= 0.0);
    }

    /// Lean: `gammaPnL_symmetric` — gamma P&L is the same for +dS and -dS.
    #[test]
    fn prop_gamma_pnl_symmetric(
        gamma in -5.0f64..5.0,
        ds in 0.001f64..100.0,
    ) {
        let h = DeltaHedge::new(0.5, gamma, -0.01);
        let diff = (h.gamma_pnl(ds) - h.gamma_pnl(-ds)).abs();
        prop_assert!(diff < 1e-10, "symmetry violated: diff={}", diff);
    }

    /// Lean: `vol_arb_profit` — realized > implied with long gamma => positive P&L.
    #[test]
    fn prop_vol_arb_profit(
        gamma in 0.001f64..1.0,
        spot in 1.0f64..500.0,
        implied in 0.01f64..0.5,
        spread in 0.001f64..0.5,
        dt in 0.001f64..1.0,
    ) {
        let realized = implied + spread;
        let pnl = vol_arb_pnl(gamma, spot, realized, implied, dt);
        prop_assert!(pnl > 0.0, "vol arb should profit: pnl={}", pnl);
    }
}
