//! # pythia-stochastic-ito
//!
//! Verified discrete Ito formula and delta-hedge gamma PnL.
//!
//! ## Lean specification (`Pythia.Finance.ItoDiscrete`)
//!
//! - **Taylor 2nd order**: f(x+dx) = f(x) + f'*dx + (1/2)*f''*dx^2 + R (`taylorSecondOrder`)
//! - **Ito correction**: (1/2)*f''*dx^2 (`itoCorrection`)
//! - **Correction nonneg for convex**: f'' >= 0 => correction >= 0 (`itoCorrection_nonneg`)
//! - **Correction nonpos for concave**: f'' <= 0 => correction <= 0 (`itoCorrection_nonpos`)
//! - **Delta hedge PnL**: (1/2)*gamma*dS^2 (`deltaHedgePnL`)
//! - **Long gamma nonneg**: gamma >= 0 => PnL >= 0 (`deltaHedgePnL_nonneg`)
//! - **PnL symmetric**: PnL(dS) = PnL(-dS) (`deltaHedgePnL_symmetric`)
//! - **Zero move zero PnL** (`deltaHedgePnL_zero_move`)

/// Second-order Taylor expansion: f(x+dx) = fx + f'*dx + (1/2)*f''*dx^2 + remainder.
/// # Lean: `taylorSecondOrder`
#[inline(always)]
pub fn taylor_second_order(fx: f64, fprime: f64, fprimeprime: f64, dx: f64, remainder: f64) -> f64 {
    fx + fprime * dx + fprimeprime / 2.0 * dx * dx + remainder
}

/// Ito correction term: (1/2) * f''(x) * dx^2.
/// # Lean: `itoCorrection`
#[inline(always)]
pub fn ito_correction(fprimeprime: f64, dx: f64) -> f64 {
    fprimeprime / 2.0 * dx * dx
}

/// Delta-hedge PnL: (1/2) * gamma * dS^2.
/// # Lean: `deltaHedgePnL`
#[inline(always)]
pub fn delta_hedge_pnl(gamma: f64, ds: f64) -> f64 {
    ito_correction(gamma, ds)
}

/// Check that Taylor decomposition equals fx + f'*dx + ito_correction + R.
/// # Lean: `taylorSecondOrder_decompose`
pub fn check_taylor_decompose(fx: f64, fprime: f64, fprimeprime: f64, dx: f64, remainder: f64, tol: f64) -> bool {
    let lhs = taylor_second_order(fx, fprime, fprimeprime, dx, remainder);
    let rhs = fx + fprime * dx + ito_correction(fprimeprime, dx) + remainder;
    (lhs - rhs).abs() < tol
}

/// Check PnL symmetry: PnL(gamma, dS) == PnL(gamma, -dS).
/// # Lean: `deltaHedgePnL_symmetric`
pub fn check_pnl_symmetric(gamma: f64, ds: f64, tol: f64) -> bool {
    (delta_hedge_pnl(gamma, ds) - delta_hedge_pnl(gamma, -ds)).abs() < tol
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ito_correction_nonneg_convex() {
        // f'' = 2.0 >= 0 => correction >= 0
        assert!(ito_correction(2.0, 0.5) >= 0.0);
        assert!(ito_correction(0.0, 1.0) >= 0.0);
    }

    #[test]
    fn ito_correction_nonpos_concave() {
        // f'' = -3.0 <= 0 => correction <= 0
        assert!(ito_correction(-3.0, 0.5) <= 0.0);
    }

    #[test]
    fn delta_hedge_pnl_nonneg_long_gamma() {
        assert!(delta_hedge_pnl(1.5, 0.3) >= 0.0);
        assert!(delta_hedge_pnl(0.0, 1.0) >= 0.0);
    }

    #[test]
    fn pnl_symmetric() {
        assert!(check_pnl_symmetric(2.0, 0.7, 1e-12));
        assert!(check_pnl_symmetric(0.5, -1.2, 1e-12));
    }

    #[test]
    fn pnl_zero_move() {
        assert!((delta_hedge_pnl(5.0, 0.0) - 0.0).abs() < 1e-15);
    }

    #[test]
    fn taylor_decompose() {
        assert!(check_taylor_decompose(10.0, 2.0, 0.5, 0.1, 0.001, 1e-12));
    }
}
