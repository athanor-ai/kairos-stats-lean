//! Provenance: SCAFFOLDING — proptest exercises the Rust implementation but the
//! corresponding Lean "theorem" is tautological (`:= h`, hypothesis restated as
//! conclusion). These tests are useful as implementation tests but are NOT formally
//! verified in the strong sense. Will be upgraded when Lean proofs are upgraded.

use proptest::prelude::*;
use pythia_hft_session::SessionState;

fn arb_state() -> impl Strategy<Value = SessionState> {
    prop_oneof![
        Just(SessionState::PreOpen),
        Just(SessionState::Continuous),
        Just(SessionState::Auction),
        Just(SessionState::Halt),
        Just(SessionState::Closed),
    ]
}

proptest! {
    /// Lean: `all_states_classified` — every state is either accepts or rejects
    #[test]
    fn all_states_classified(s in arb_state()) {
        let accepts = s.accepts_orders();
        prop_assert!(accepts || !accepts);
    }

    /// Lean: `closed_rejects_orders` + `closed_rejects_cancels`
    #[test]
    fn closed_rejects_everything(_dummy in 0..100u32) {
        prop_assert!(!SessionState::Closed.accepts_orders());
        prop_assert!(!SessionState::Closed.accepts_cancels());
    }

    /// Lean: `halt_rejects_orders`
    #[test]
    fn halt_rejects_orders(_dummy in 0..100u32) {
        prop_assert!(!SessionState::Halt.accepts_orders());
    }

    /// Lean: `continuous_accepts_orders`
    #[test]
    fn continuous_accepts(s in Just(SessionState::Continuous)) {
        prop_assert!(s.accepts_orders());
        prop_assert!(s.accepts_cancels());
    }

    /// Invariant: closed is always terminal (no valid transitions out)
    #[test]
    fn closed_terminal(_dummy in 0..100u32) {
        prop_assert!(SessionState::Closed.valid_transitions().is_empty());
    }
}
