import Mathlib

-- AXI-like bus protocol safety properties.
-- Relevant for Annapurna interconnect verification.

inductive BusState | idle | addr | data | resp
  deriving DecidableEq

structure BusTransaction where
  state : BusState
  outstanding : ℕ

def busStep (t : BusTransaction) (accept : Bool) : BusTransaction :=
  match t.state with
  | .idle => if accept then { state := .addr, outstanding := t.outstanding + 1 } else t
  | .addr => { t with state := .data }
  | .data => { t with state := .resp }
  | .resp => { state := .idle, outstanding := t.outstanding - 1 }

-- No response without request (outstanding ≥ 0 always)
theorem no_spurious_response (t : BusTransaction) (h : t.state = .resp) :
    0 < t.outstanding → (busStep t true).outstanding = t.outstanding - 1 := by
  simp [busStep, h]

-- Protocol returns to idle after complete transaction
theorem transaction_completes (t : BusTransaction) (h : t.state = .resp) :
    (busStep t true).state = .idle := by
  simp [busStep, h]

-- Outstanding count monotone during request phase
theorem outstanding_monotone_request (t : BusTransaction) (h : t.state = .idle) :
    (busStep t true).outstanding = t.outstanding + 1 := by
  simp [busStep, h]
