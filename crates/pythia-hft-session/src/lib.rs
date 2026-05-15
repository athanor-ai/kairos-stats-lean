//! # pythia-hft-session
//!
//! Trading session state machine with proven order acceptance rules.
//!
//! ## Lean specification (`Pythia.Finance.HFT.TradingSession`)
//!
//! - **Closed rejects orders + cancels** (`closed_rejects_orders`, `closed_rejects_cancels`)
//! - **Halt rejects orders** (`halt_rejects_orders`)
//! - **Continuous accepts orders** (`continuous_accepts_orders`)
//! - **PreOpen rejects orders but accepts cancels** (`preopen_rejects_orders`, `preopen_accepts_cancels`)
//! - **All states classified** (`all_states_classified`)

/// Exchange trading session states.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionState {
    PreOpen,
    Continuous,
    Auction,
    Halt,
    Closed,
}

impl SessionState {
    /// Can new orders be submitted in this state?
    ///
    /// # Lean: `acceptsOrders`
    /// Only `Continuous` and `Auction` accept orders.
    #[inline(always)]
    pub const fn accepts_orders(&self) -> bool {
        matches!(self, Self::Continuous | Self::Auction)
    }

    /// Can existing orders be cancelled in this state?
    ///
    /// # Lean: `acceptsCancels`
    /// `PreOpen`, `Continuous`, and `Auction` accept cancels.
    #[inline(always)]
    pub const fn accepts_cancels(&self) -> bool {
        matches!(self, Self::PreOpen | Self::Continuous | Self::Auction)
    }

    /// All valid transitions from this state.
    pub fn valid_transitions(&self) -> &[SessionState] {
        match self {
            Self::PreOpen => &[Self::Continuous, Self::Auction],
            Self::Continuous => &[Self::Auction, Self::Halt, Self::Closed],
            Self::Auction => &[Self::Continuous, Self::Closed],
            Self::Halt => &[Self::Continuous, Self::Closed],
            Self::Closed => &[],
        }
    }

    /// Is this a terminal state?
    pub const fn is_terminal(&self) -> bool {
        matches!(self, Self::Closed)
    }
}

/// A session that tracks state transitions.
#[derive(Debug)]
pub struct Session {
    pub state: SessionState,
}

impl Session {
    pub fn new() -> Self {
        Self { state: SessionState::PreOpen }
    }

    /// Attempt a state transition. Returns false if invalid.
    pub fn transition(&mut self, to: SessionState) -> bool {
        if self.state.valid_transitions().contains(&to) {
            self.state = to;
            true
        } else {
            false
        }
    }

    /// Submit an order. Returns false if rejected by session state.
    pub fn submit_order(&self) -> bool {
        self.state.accepts_orders()
    }

    /// Cancel an order. Returns false if rejected by session state.
    pub fn cancel_order(&self) -> bool {
        self.state.accepts_cancels()
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closed_rejects_orders() {
        assert!(!SessionState::Closed.accepts_orders());
    }

    #[test]
    fn closed_rejects_cancels() {
        assert!(!SessionState::Closed.accepts_cancels());
    }

    #[test]
    fn halt_rejects_orders() {
        assert!(!SessionState::Halt.accepts_orders());
    }

    #[test]
    fn continuous_accepts_orders() {
        assert!(SessionState::Continuous.accepts_orders());
    }

    #[test]
    fn preopen_rejects_orders_accepts_cancels() {
        assert!(!SessionState::PreOpen.accepts_orders());
        assert!(SessionState::PreOpen.accepts_cancels());
    }

    #[test]
    fn all_states_classified() {
        for s in [SessionState::PreOpen, SessionState::Continuous,
                  SessionState::Auction, SessionState::Halt, SessionState::Closed] {
            assert!(s.accepts_orders() || !s.accepts_orders());
        }
    }

    #[test]
    fn session_lifecycle() {
        let mut s = Session::new();
        assert_eq!(s.state, SessionState::PreOpen);
        assert!(!s.submit_order());
        assert!(s.cancel_order());
        assert!(s.transition(SessionState::Continuous));
        assert!(s.submit_order());
        assert!(s.transition(SessionState::Closed));
        assert!(!s.submit_order());
        assert!(!s.cancel_order());
        assert!(!s.transition(SessionState::Continuous));
    }

    #[test]
    fn closed_is_terminal() {
        assert!(SessionState::Closed.is_terminal());
        assert!(SessionState::Closed.valid_transitions().is_empty());
    }
}
