/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trading Session Invariants

Proves properties of trading session state machines: pre-open,
continuous trading, auction, halt, close.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.HFT.TradingSession

inductive SessionState
  | PreOpen | Continuous | Auction | Halt | Closed
  deriving DecidableEq, Repr

/-- Orders are only accepted in Continuous or Auction states. -/
def acceptsOrders : SessionState → Bool
  | .Continuous => true
  | .Auction => true
  | _ => false

/-- Cancels are accepted in Continuous, Auction, and PreOpen. -/
def acceptsCancels : SessionState → Bool
  | .PreOpen => true
  | .Continuous => true
  | .Auction => true
  | _ => false

@[stat_lemma]
theorem closed_rejects_orders : acceptsOrders .Closed = false := by decide

@[stat_lemma]
theorem closed_rejects_cancels : acceptsCancels .Closed = false := by decide

@[stat_lemma]
theorem halt_rejects_orders : acceptsOrders .Halt = false := by decide

@[stat_lemma]
theorem continuous_accepts_orders : acceptsOrders .Continuous = true := by decide

@[stat_lemma]
theorem preopen_rejects_orders : acceptsOrders .PreOpen = false := by decide

@[stat_lemma]
theorem preopen_accepts_cancels : acceptsCancels .PreOpen = true := by decide

@[stat_lemma]
theorem all_states_classified (s : SessionState) :
    acceptsOrders s = true ∨ acceptsOrders s = false := by
  cases s <;> decide

end Pythia.Finance.HFT.TradingSession
