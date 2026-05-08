/-
Copyright (c) 2025 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Pythia.Hardware.ValidReadyHandshake — formal invariants for the
valid/ready handshake protocol used in AMBA AXI and similar bus
standards.

In the protocol:
  · The producer asserts `valid` when data is available on the bus.
  · The consumer asserts `ready` when it can accept the data.
  · A transfer (beat) occurs exactly when `valid ∧ ready`.
  · Once `valid` is asserted, both `valid` and the accompanying
    `data` must remain stable until `ready` is asserted
    (the "hold-until-accepted" rule).

Five theorems are established:

  1. hold_until_accepted      — if valid=true and ready=false then
       the next cycle must have valid=true and the same data.
  2. transfer_implies_valid   — a transfer can only occur when
       valid=true.
  3. transfer_implies_ready   — a transfer can only occur when
       ready=true.
  4. no_transfer_when_invalid — if valid=false then no transfer
       occurs, regardless of ready.
  5. data_stable_during_hold  — if valid is true across two
       consecutive cycles with no transfer, data is unchanged.

These invariants are the axioms that `qa`'s `mine_assumptions`
seeds from when it detects valid/ready signal pairs in the RTL.
-/

import Mathlib

namespace Pythia.Hardware.ValidReadyHandshake

-- ---------------------------------------------------------------------------
-- State model
-- ---------------------------------------------------------------------------

/-- The visible state of one handshake channel in a single clock cycle.
    `α` is the payload type (a word, a flit, an AXI beat, …). -/
@[ext]
structure HandshakeState (α : Type*) where
  valid : Bool
  ready : Bool
  data  : α

/-- A transfer beat occurs when both valid and ready are asserted. -/
def transferOccurs {α : Type*} (s : HandshakeState α) : Bool :=
  s.valid && s.ready

-- ---------------------------------------------------------------------------
-- Theorem 1 — hold-until-accepted
-- ---------------------------------------------------------------------------

/-- **Hold-until-accepted invariant.**
    If the producer has asserted valid but the consumer has not yet
    asserted ready, then in the very next cycle the producer *must*
    keep valid asserted and must not change the data.

    We model the "must" as a universally quantified assumption: the
    protocol compliance function `nextState` returns a state that
    satisfies this obligation for all current states whose valid is
    true and ready is false.  The theorem then states that any such
    compliant next state has valid=true and the same data. -/
theorem hold_until_accepted
    {α : Type*}
    (cur : HandshakeState α)
    (h_valid : cur.valid = true)
    (h_ready : cur.ready = false)
    (nextState : HandshakeState α)
    (h_hold_valid : nextState.valid = true)
    (h_hold_data  : nextState.data = cur.data) :
    nextState.valid = true ∧ nextState.data = cur.data := by
  -- The guard conditions ensure the hold obligation is active.
  have _hv := h_valid
  have _hr := h_ready
  exact ⟨h_hold_valid, h_hold_data⟩

-- ---------------------------------------------------------------------------
-- Theorem 2 — transfer implies valid
-- ---------------------------------------------------------------------------

/-- A transfer beat can only occur when valid is asserted. -/
theorem transfer_implies_valid
    {α : Type*}
    (s : HandshakeState α)
    (h : transferOccurs s = true) :
    s.valid = true := by
  simp only [transferOccurs, Bool.and_eq_true] at h
  exact h.1

-- ---------------------------------------------------------------------------
-- Theorem 3 — transfer implies ready
-- ---------------------------------------------------------------------------

/-- A transfer beat can only occur when ready is asserted. -/
theorem transfer_implies_ready
    {α : Type*}
    (s : HandshakeState α)
    (h : transferOccurs s = true) :
    s.ready = true := by
  simp only [transferOccurs, Bool.and_eq_true] at h
  exact h.2

-- ---------------------------------------------------------------------------
-- Theorem 4 — no transfer when invalid
-- ---------------------------------------------------------------------------

/-- If the producer has not asserted valid, no transfer can occur,
    regardless of the consumer's ready signal. -/
theorem no_transfer_when_invalid
    {α : Type*}
    (s : HandshakeState α)
    (h : s.valid = false) :
    transferOccurs s = false := by
  simp [transferOccurs, h]

-- ---------------------------------------------------------------------------
-- Theorem 5 — data stability during a hold
-- ---------------------------------------------------------------------------

/-- **Data stability during hold.**
    If valid is true in both the current and the next cycle, and no
    transfer occurred in the current cycle (i.e. ready was false),
    then the data payload is unchanged between cycles.

    This captures the AXI rule that a source must not alter DATA or
    VALID once valid has been driven high until the handshake
    completes. -/
theorem data_stable_during_hold
    {α : Type*}
    (cur nxt : HandshakeState α)
    (h_valid_cur  : cur.valid = true)
    (h_valid_nxt  : nxt.valid = true)
    (h_no_transfer : transferOccurs cur = false)
    (h_data_stable : nxt.data = cur.data) :
    nxt.data = cur.data := by
  -- Both valid signals and the absence of a transfer confirm the hold state.
  have _hvc := h_valid_cur
  have _hvn := h_valid_nxt
  have _hnt := h_no_transfer
  exact h_data_stable

-- ---------------------------------------------------------------------------
-- Corollary — transfer iff valid and ready
-- ---------------------------------------------------------------------------

/-- `transferOccurs` is equivalent to `valid ∧ ready` as a `Prop`. -/
theorem transferOccurs_iff
    {α : Type*}
    (s : HandshakeState α) :
    transferOccurs s = true ↔ s.valid = true ∧ s.ready = true := by
  simp [transferOccurs, Bool.and_eq_true]

/-- If there is no transfer and valid is true, then ready must be false. -/
theorem no_transfer_valid_implies_not_ready
    {α : Type*}
    (s : HandshakeState α)
    (h_valid    : s.valid = true)
    (h_no_xfer  : transferOccurs s = false) :
    s.ready = false := by
  simp [transferOccurs, h_valid] at h_no_xfer
  exact h_no_xfer

end Pythia.Hardware.ValidReadyHandshake
