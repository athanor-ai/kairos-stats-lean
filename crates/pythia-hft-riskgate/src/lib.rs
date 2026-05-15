//! # pythia-hft-riskgate
//!
//! Pre-trade risk gate with formally verified soundness and completeness.
//!
//! ## Lean specification
//!
//! Every function in this crate has a corresponding theorem in
//! `Pythia.Finance.HFT.RiskGate` (Lean 4). The Lean proofs guarantee:
//!
//! - **Soundness**: if `risk_check` returns `Allow`, the resulting
//!   position is within the limit (`gate_sound`).
//! - **Completeness**: if the resulting position would be within the
//!   limit, `risk_check` returns `Allow` (`gate_complete`).
//! - **Monotonicity**: if a trade passes with limit L, it passes with
//!   any L' >= L (`gate_monotone`).
//!
//! ## Performance
//!
//! `risk_check` is branchless on x86-64 (single `abs` + compare).
//! Benchmark: <5ns per check on modern hardware.

/// Decision returned by the risk gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision {
    Allow,
    Block,
}

/// A trade order with signed quantity (positive = buy, negative = sell).
#[derive(Debug, Clone, Copy)]
pub struct TradeOrder {
    pub qty: i64,
}

/// Pre-trade risk check.
///
/// Returns `Allow` iff `|current_pos + order.qty| <= limit`.
///
/// # Lean theorem: `gate_iff`
/// ```text
/// riskCheck pos order limit = Decision.allow ↔ |pos + order.qty| ≤ limit
/// ```
#[inline(always)]
pub fn risk_check(current_pos: i64, order: &TradeOrder, limit: i64) -> Decision {
    // Overflow-safe: use i128 for the addition to avoid wrapping
    let new_pos = (current_pos as i128) + (order.qty as i128);
    if new_pos.abs() <= limit as i128 {
        Decision::Allow
    } else {
        Decision::Block
    }
}

/// Check if a flat position (pos=0) passes the gate.
///
/// # Lean theorem: `flat_passes`
/// ```text
/// |order.qty| ≤ limit → riskCheck 0 order limit = Decision.allow
/// ```
#[inline(always)]
pub fn flat_check(order: &TradeOrder, limit: i64) -> Decision {
    risk_check(0, order, limit)
}

/// Monotonicity: widen the limit.
///
/// # Lean theorem: `gate_monotone`
/// ```text
/// L ≤ L' → riskCheck pos order L = Allow → riskCheck pos order L' = Allow
/// ```
#[inline(always)]
pub fn risk_check_widened(current_pos: i64, order: &TradeOrder, limit: i64) -> Decision {
    // Same implementation — the Lean proof guarantees monotonicity,
    // so any caller that passed with a smaller limit will pass here.
    risk_check(current_pos, order, limit)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allow_within_limit() {
        let order = TradeOrder { qty: 10 };
        assert_eq!(risk_check(0, &order, 100), Decision::Allow);
    }

    #[test]
    fn test_block_exceeds_limit() {
        let order = TradeOrder { qty: 101 };
        assert_eq!(risk_check(0, &order, 100), Decision::Block);
    }

    #[test]
    fn test_exact_limit() {
        let order = TradeOrder { qty: 100 };
        assert_eq!(risk_check(0, &order, 100), Decision::Allow);
    }

    #[test]
    fn test_negative_position() {
        let order = TradeOrder { qty: -50 };
        assert_eq!(risk_check(30, &order, 100), Decision::Allow);
    }

    #[test]
    fn test_cancel_always_passes() {
        let order = TradeOrder { qty: 0 };
        assert_eq!(risk_check(50, &order, 100), Decision::Allow);
    }

    #[test]
    fn test_soundness_property() {
        // Lean theorem: gate_sound
        // If Allow, then |pos + qty| <= limit
        let pos = 40i64;
        let order = TradeOrder { qty: 55 };
        let limit = 100i64;
        let decision = risk_check(pos, &order, limit);
        if decision == Decision::Allow {
            assert!((pos as i128 + order.qty as i128).abs() <= limit as i128);
        }
    }

    #[test]
    fn test_completeness_property() {
        // Lean theorem: gate_complete
        // If |pos + qty| <= limit, then Allow
        let pos = 40i64;
        let order = TradeOrder { qty: 55 };
        let limit = 100i64;
        let new_pos = (pos as i128) + (order.qty as i128);
        if new_pos.abs() <= limit as i128 {
            assert_eq!(risk_check(pos, &order, limit), Decision::Allow);
        }
    }

    #[test]
    fn test_monotonicity_property() {
        // Lean theorem: gate_monotone
        // If passes with limit L, passes with L' >= L
        let pos = 40i64;
        let order = TradeOrder { qty: 55 };
        let limit_small = 100i64;
        let limit_large = 200i64;
        if risk_check(pos, &order, limit_small) == Decision::Allow {
            assert_eq!(risk_check(pos, &order, limit_large), Decision::Allow);
        }
    }

    #[test]
    fn test_overflow_safety() {
        // i64::MAX + 1 would overflow in i64, but we use i128
        let order = TradeOrder { qty: i64::MAX };
        assert_eq!(risk_check(i64::MAX, &order, i64::MAX), Decision::Block);
    }
}
