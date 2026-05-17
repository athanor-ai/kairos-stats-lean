//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (mul_nonneg, div_nonneg, sq_nonneg, mul_nonpos_of_nonpos_of_nonneg, ring).

use proptest::prelude::*;
use pythia_stochastic_ito::*;

proptest! {
    /// Lean: `itoCorrection_nonneg`
    /// f'' >= 0 implies ito correction >= 0.
    #[test]
    fn correction_nonneg_convex(fpp in 0.0f64..10.0, dx in -5.0f64..5.0) {
        prop_assert!(ito_correction(fpp, dx) >= -1e-15);
    }

    /// Lean: `itoCorrection_nonpos`
    /// f'' <= 0 implies ito correction <= 0.
    #[test]
    fn correction_nonpos_concave(fpp in -10.0f64..0.0, dx in -5.0f64..5.0) {
        prop_assert!(ito_correction(fpp, dx) <= 1e-15);
    }

    /// Lean: `deltaHedgePnL_symmetric`
    /// Gamma PnL is symmetric in dS.
    #[test]
    fn pnl_symmetric(gamma in -10.0f64..10.0, ds in -5.0f64..5.0) {
        prop_assert!(check_pnl_symmetric(gamma, ds, 1e-10));
    }

    /// Lean: `deltaHedgePnL_nonneg` + `deltaHedgePnL_zero_move`
    /// Long gamma (>= 0) has nonneg PnL; zero move gives zero.
    #[test]
    fn pnl_long_gamma_nonneg(gamma in 0.0f64..10.0, ds in -5.0f64..5.0) {
        prop_assert!(delta_hedge_pnl(gamma, ds) >= -1e-15);
        prop_assert!((delta_hedge_pnl(gamma, 0.0)).abs() < 1e-15);
    }
}
