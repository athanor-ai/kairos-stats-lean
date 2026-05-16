//! # pythia-risk-leverage
//!
//! Verified leverage decay (volatility drag) for daily-rebalanced leveraged ETFs.
//!
//! ## Lean specification (`Pythia.Finance.Risk.LeverageDecay`)
//!
//! - **Zero return** (`leveragedReturn_zero`)
//! - **Two-period compounding commutativity** (`compoundTwoPeriod_comm`)
//! - **Fundamental drag identity** (`leverageDrag_identity`)
//! - **Drag non-negative for same-sign returns** (`leverageDrag_nonneg_of_same_sign`)
//! - **Unit leverage zero drag** (`leverageDrag_zero_at_unit_leverage`)
//! - **Drag monotone in leverage** (`leverageDrag_abs_mono_L`)

/// Single-period leveraged ETF return: L * r.
///
/// # Lean: `leveragedReturn`
#[inline(always)]
pub fn leveraged_return(l: f64, r: f64) -> f64 {
    l * r
}

/// Two-period discrete compounding: (1 + r1)(1 + r2) - 1.
///
/// # Lean: `compoundTwoPeriod`
#[inline(always)]
pub fn compound_two_period(r1: f64, r2: f64) -> f64 {
    (1.0 + r1) * (1.0 + r2) - 1.0
}

/// Volatility drag (leverage decay) term: L * (L - 1) * r1 * r2.
///
/// # Lean: `leverageDrag`
#[inline(always)]
pub fn leverage_drag(l: f64, r1: f64, r2: f64) -> f64 {
    l * (l - 1.0) * r1 * r2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leveraged_return_zero() {
        assert_eq!(leveraged_return(3.0, 0.0), 0.0);
        assert_eq!(leveraged_return(-2.0, 0.0), 0.0);
    }

    #[test]
    fn compound_two_period_comm() {
        let a = compound_two_period(0.05, -0.03);
        let b = compound_two_period(-0.03, 0.05);
        assert!((a - b).abs() < 1e-10);
    }

    #[test]
    fn drag_identity() {
        let l = 3.0;
        let r1 = 0.02;
        let r2 = -0.01;
        let lhs = compound_two_period(leveraged_return(l, r1), leveraged_return(l, r2))
            - leveraged_return(l, compound_two_period(r1, r2));
        let rhs = leverage_drag(l, r1, r2);
        assert!((lhs - rhs).abs() < 1e-10);
    }

    #[test]
    fn drag_nonneg_same_sign() {
        // L >= 1, same-sign returns => drag >= 0
        assert!(leverage_drag(2.0, 0.05, 0.03) >= 0.0);
        assert!(leverage_drag(3.0, -0.02, -0.01) >= 0.0);
    }

    #[test]
    fn drag_zero_at_unit_leverage() {
        assert_eq!(leverage_drag(1.0, 0.05, 0.03), 0.0);
        assert_eq!(leverage_drag(1.0, -0.02, 0.07), 0.0);
    }

    #[test]
    fn drag_mono_in_leverage() {
        let r1 = 0.03;
        let r2 = 0.02;
        assert!(leverage_drag(2.0, r1, r2) <= leverage_drag(3.0, r1, r2));
    }
}
