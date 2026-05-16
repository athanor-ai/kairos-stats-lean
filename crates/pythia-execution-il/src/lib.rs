//! Impermanent Loss in a Constant-Product AMM
//!
//! Implements the algebraic kernel from:
//! Pythia/Finance/Execution/ImpermanentLoss.lean
//!
//! IL(r) = (2*sqrt(r)) / (1 + r) - 1
//! where r = p / p0 is the relative price-change factor.

/// Impermanent loss for a constant-product AMM at relative-price ratio r.
/// IL(r) = (2*sqrt(r)) / (1 + r) - 1
///
/// For r > 0: IL(r) <= 0 (LP underperforms HODL).
/// At r = 1: IL(1) = 0 (no price change, no loss).
pub fn impermanent_loss(r: f64) -> f64 {
    (2.0 * r.sqrt()) / (1.0 + r) - 1.0
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: impermanentLoss_at_one: IL(1) = 0
    #[test]
    fn test_il_at_one() {
        let il = impermanent_loss(1.0);
        assert!((il - 0.0).abs() < 1e-15);
    }

    /// Lean: impermanentLoss_nonpos for r > 0
    #[test]
    fn test_il_nonpos_r_half() {
        let il = impermanent_loss(0.5);
        assert!(il <= 0.0);
    }

    /// Lean: impermanentLoss_nonpos for r > 1
    #[test]
    fn test_il_nonpos_r_two() {
        let il = impermanent_loss(2.0);
        assert!(il <= 0.0);
    }

    /// Symmetry-like property: IL at r and 1/r have same sign (both non-positive)
    #[test]
    fn test_il_both_sides_nonpos() {
        let r = 4.0;
        assert!(impermanent_loss(r) <= 0.0);
        assert!(impermanent_loss(1.0 / r) <= 0.0);
    }

    /// Known value: IL(4) = 2*2/5 - 1 = -0.2
    #[test]
    fn test_il_known_value() {
        let il = impermanent_loss(4.0);
        // 2*sqrt(4)/(1+4) - 1 = 4/5 - 1 = -0.2
        assert!((il - (-0.2)).abs() < 1e-15);
    }

    /// IL approaches -1 as r -> infinity (total loss)
    #[test]
    fn test_il_large_r() {
        let il = impermanent_loss(1e10);
        // 2*sqrt(1e10)/(1+1e10) - 1 ~ 2e5/1e10 - 1 ~ -1
        assert!(il < -0.99);
        assert!(il >= -1.0);
    }
}
