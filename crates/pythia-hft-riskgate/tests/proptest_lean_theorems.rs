//! Property tests derived from Lean theorems in Pythia.Finance.HFT.RiskGate.
//!
//! Each test corresponds to a named Lean theorem. The Lean proof guarantees
//! the property holds for ALL inputs; proptest verifies the Rust implementation
//! matches the spec on random inputs.

use proptest::prelude::*;
use pythia_hft_riskgate::{risk_check, Decision, TradeOrder};

// Lean theorem: gate_sound
// If risk_check returns Allow, then |pos + qty| <= limit.
proptest! {
    #[test]
    fn gate_sound(
        pos in -1_000_000i64..1_000_000,
        qty in -1_000_000i64..1_000_000,
        limit in 0i64..2_000_000,
    ) {
        let order = TradeOrder { qty };
        let decision = risk_check(pos, &order, limit);
        if decision == Decision::Allow {
            let new_pos = (pos as i128) + (qty as i128);
            prop_assert!(new_pos.abs() <= limit as i128,
                "gate_sound violated: pos={}, qty={}, limit={}, |new_pos|={}",
                pos, qty, limit, new_pos.abs());
        }
    }
}

// Lean theorem: gate_complete
// If |pos + qty| <= limit, then risk_check returns Allow.
proptest! {
    #[test]
    fn gate_complete(
        pos in -1_000_000i64..1_000_000,
        qty in -1_000_000i64..1_000_000,
        limit in 0i64..2_000_000,
    ) {
        let new_pos = (pos as i128) + (qty as i128);
        if new_pos.abs() <= limit as i128 {
            let order = TradeOrder { qty };
            let decision = risk_check(pos, &order, limit);
            prop_assert_eq!(decision, Decision::Allow,
                "gate_complete violated: pos={}, qty={}, limit={}, |new_pos|={}",
                pos, qty, limit, new_pos.abs());
        }
    }
}

// Lean theorem: gate_monotone
// If risk_check(pos, order, L) = Allow and L <= L', then
// risk_check(pos, order, L') = Allow.
proptest! {
    #[test]
    fn gate_monotone(
        pos in -1_000_000i64..1_000_000,
        qty in -1_000_000i64..1_000_000,
        limit_small in 0i64..1_000_000,
        limit_delta in 0i64..1_000_000,
    ) {
        let limit_large = limit_small.saturating_add(limit_delta);
        let order = TradeOrder { qty };
        if risk_check(pos, &order, limit_small) == Decision::Allow {
            let decision_large = risk_check(pos, &order, limit_large);
            prop_assert_eq!(decision_large, Decision::Allow,
                "gate_monotone violated: pos={}, qty={}, L={}, L'={}",
                pos, qty, limit_small, limit_large);
        }
    }
}

// Lean theorem: flat_passes
// If |qty| <= limit, then risk_check(0, order, limit) = Allow.
proptest! {
    #[test]
    fn flat_passes(
        qty in -1_000_000i64..1_000_000,
        limit in 0i64..2_000_000,
    ) {
        if qty.unsigned_abs() as i128 <= limit as i128 {
            let order = TradeOrder { qty };
            let decision = risk_check(0, &order, limit);
            prop_assert_eq!(decision, Decision::Allow,
                "flat_passes violated: qty={}, limit={}", qty, limit);
        }
    }
}

// Lean theorem: cancel_passes
// risk_check(pos, {qty: 0}, limit) = Allow when |pos| <= limit.
proptest! {
    #[test]
    fn cancel_passes(
        pos in -1_000_000i64..1_000_000,
        limit in 0i64..2_000_000,
    ) {
        if (pos as i128).abs() <= limit as i128 {
            let order = TradeOrder { qty: 0 };
            let decision = risk_check(pos, &order, limit);
            prop_assert_eq!(decision, Decision::Allow,
                "cancel_passes violated: pos={}, limit={}", pos, limit);
        }
    }
}
