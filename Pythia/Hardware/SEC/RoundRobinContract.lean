/-
Pythia.Hardware.SEC.RoundRobinContract — abstract refinement
contract for round-robin arbiter blocks (e.g. `arb_widget` in
the toy_fifo_chain demo).

This contract covers the SAFETY form of round-robin only:
"the next-active source is the cyclic successor of the current
active source given a request signal." The LIVENESS form
("every requesting source is eventually served") is a temporal
property and is NOT covered here; that obligation gates on
the `gated_on_temporal_verifier` slot in the verdict mix and
will be discharged by a separate temporal-property checker
when that vertical lands.

Reference: 2026-05-04 SEC pivot, ATH-XXX. the customer's
"EBMC fine for now" reads as accepting the safety form for
this iteration.
-/
import Mathlib

namespace Pythia.Hardware.SEC

/-! ## Abstract round-robin state -/

/-- The abstract state of a round-robin arbiter over `N` sources.
The `active` index is the source the arbiter would grant first
in the cyclic scan. -/
structure RoundRobinState (N : ℕ) where
  active : Fin (N + 1)
  deriving Repr

/-- The abstract input on a round-robin clock cycle: a request
bit-vector indicating which sources are currently asserting. -/
structure RoundRobinInput (N : ℕ) where
  req : Fin (N + 1) → Bool
  deriving Repr

/-- The abstract output on a round-robin clock cycle: which
source got granted (if any), and a valid bit. -/
structure RoundRobinOutput (N : ℕ) where
  grant : Fin (N + 1)
  grant_valid : Bool
  deriving Repr

/-! ## Cyclic scan helper

Given a base position `b : Fin (N+1)` and a predicate `p : Fin (N+1) → Bool`,
return the smallest cyclic offset `k ∈ [0, N+1)` such that `p ((b + k) % (N+1))`
holds, or `none` if no such `k` exists.
-/

/-- Cyclic-first-asserting helper. Scans positions `(b + k) % (N+1)`
for `k = 0, 1, …, N` and returns the first index where `p` holds. -/
noncomputable def cyclicFirst {N : ℕ} (b : Fin (N + 1)) (p : Fin (N + 1) → Bool) :
    Option (Fin (N + 1)) :=
  (List.range (N + 1)).findSome? fun k =>
    let idx : Fin (N + 1) :=
      ⟨(b.val + k) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩
    if p idx then some idx else none

/-! ## The abstract step function -/

/-- The reference round-robin step: scan cyclically from `active`
for an asserting source. If found, grant it and advance active to
the cyclic successor. If no source asserts, `active` stays put
and `grant_valid = false`. -/
noncomputable def roundRobinStep {N : ℕ}
    (s : RoundRobinState N) (i : RoundRobinInput N) :
    RoundRobinState N × RoundRobinOutput N :=
  match cyclicFirst s.active i.req with
  | some granted =>
    let next : Fin (N + 1) :=
      ⟨(granted.val + 1) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩
    (⟨next⟩, ⟨granted, true⟩)
  | none =>
    (s, ⟨s.active, false⟩)

/-! ## Refinement contract -/

/-- An RTL implementation refines the round-robin contract if its
externally-observable behaviour agrees with `roundRobinStep` for
every input sequence starting from a reset-reachable state. -/
def implementsRoundRobin {N : ℕ}
    (impl : RoundRobinState N → RoundRobinInput N →
            RoundRobinState N × RoundRobinOutput N) : Prop :=
  ∀ s i, impl s i = roundRobinStep s i

/-! ## Composition with EBMC certificate -/

/-- An EBMC-witnessed round-robin refinement. The safety form is
discharged by EBMC-induction over the abstract state machine. -/
structure RoundRobinEBMCWitness (N : ℕ)
    (impl : RoundRobinState N → RoundRobinInput N →
            RoundRobinState N × RoundRobinOutput N) where
  refines : implementsRoundRobin impl
  /-- Engine: "ebmc-bmc" or "ebmc-k_induction" (the safety form
  benefits from k-induction since it's a state-machine claim). -/
  engine : String
  /-- Hash of the EBMC transcript for auditability. -/
  transcript_hash : String

end Pythia.Hardware.SEC
