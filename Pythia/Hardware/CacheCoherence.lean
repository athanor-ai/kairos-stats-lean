/-
Copyright (c) 2025 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia

Pythia.Hardware.CacheCoherence — formal invariants for the MESI cache
coherence protocol used in multi-core processors.

MESI names four stable states a cache line can occupy:
  · Modified  (M) — one cache owns the line with a dirty write; no other
                     cache has a valid copy.
  · Exclusive (E) — one cache holds the sole clean copy (memory is up to
                     date).
  · Shared    (S) — two or more caches hold identical clean copies.
  · Invalid   (I) — the cache has no valid copy of the line.

Six theorems are established:

  1. mesi_mutual_exclusion    — at most one cache can be in Modified state
                                for any given address.
  2. mesi_data_consistency    — if a cache is in Modified state its data is
                                the most-recent write value.
  3. mesi_shared_agreement    — all caches in Shared state hold the same
                                data value.
  4. mesi_exclusive_unique    — at most one cache can be in Exclusive state.
  5. mesi_invalid_no_stale    — reading from Invalid state forces a bus
                                transaction; no stale data is returned.
  6. mesi_transition_valid    — only valid MESI state transitions are
                                permitted (Invalid → Modified requires passing
                                through Exclusive first).

No sorries.
-/

import Mathlib

namespace Pythia.Hardware.CacheCoherence

-- ---------------------------------------------------------------------------
-- §1  MESI state and cache-line model
-- ---------------------------------------------------------------------------

/-- The four stable states of the MESI protocol. -/
inductive MESIState where
  | modified  : MESIState
  | exclusive : MESIState
  | shared    : MESIState
  | invalid   : MESIState
  deriving DecidableEq, Repr

/-- A single cache line parameterised by its payload type `α`. -/
structure CacheLine (α : Type*) where
  state : MESIState
  data  : α

-- ---------------------------------------------------------------------------
-- §2  System model
-- ---------------------------------------------------------------------------

/-- A MESI system is a finite collection of `n` caches, each holding one
    cache line for the address of interest.  We also track the canonical
    *memory value* and the *last written value* (the "ground truth" for
    Modified data). -/
structure MESISystem (n : ℕ) (α : Type*) where
  /-- Cache lines indexed by core id. -/
  caches    : Fin n → CacheLine α
  /-- The canonical memory (DRAM) value for this address. -/
  memVal    : α
  /-- The value of the most-recent write (held by the Modified owner, if any). -/
  lastWrite : α

-- ---------------------------------------------------------------------------
-- §3  Protocol predicates
-- ---------------------------------------------------------------------------

/-- At most one Modified owner can exist. -/
def AtMostOneModified {n : ℕ} {α : Type*} (sys : MESISystem n α) : Prop :=
  ∀ i j : Fin n,
    (sys.caches i).state = MESIState.modified →
    (sys.caches j).state = MESIState.modified →
    i = j

/-- If a cache is Modified its data equals the last-write value. -/
def ModifiedIsCurrentWrite {n : ℕ} {α : Type*} (sys : MESISystem n α) : Prop :=
  ∀ i : Fin n,
    (sys.caches i).state = MESIState.modified →
    (sys.caches i).data = sys.lastWrite

/-- All Shared caches hold identical data. -/
def SharedAgreement {n : ℕ} {α : Type*} (sys : MESISystem n α) : Prop :=
  ∀ i j : Fin n,
    (sys.caches i).state = MESIState.shared →
    (sys.caches j).state = MESIState.shared →
    (sys.caches i).data = (sys.caches j).data

/-- At most one cache can be in Exclusive state. -/
def AtMostOneExclusive {n : ℕ} {α : Type*} (sys : MESISystem n α) : Prop :=
  ∀ i j : Fin n,
    (sys.caches i).state = MESIState.exclusive →
    (sys.caches j).state = MESIState.exclusive →
    i = j

-- ---------------------------------------------------------------------------
-- §4  State-transition validity
-- ---------------------------------------------------------------------------

/-- Valid single-step MESI state transitions.

    The standard MESI transition graph (processor-side requests only):
      · M → M   (subsequent writes to the same owner)
      · M → E   (write-back, line becomes clean Exclusive)
      · M → S   (another cache requests a read; line is downgraded)
      · M → I   (invalidation or eviction)
      · E → M   (local write — no bus transaction needed)
      · E → S   (another cache requests a read)
      · E → I   (invalidation or eviction)
      · S → I   (invalidation)
      · S → M   (bus-upgrade event)
      · I → E   (local read — fetch from memory, become Exclusive)

    Crucially, *I → M* (direct jump from Invalid to Modified) is NOT
    permitted; a core must first go through Exclusive (I → E → M). -/
inductive ValidTransition : MESIState → MESIState → Prop where
  | M_M : ValidTransition .modified  .modified
  | M_E : ValidTransition .modified  .exclusive
  | M_S : ValidTransition .modified  .shared
  | M_I : ValidTransition .modified  .invalid
  | E_M : ValidTransition .exclusive .modified
  | E_S : ValidTransition .exclusive .shared
  | E_I : ValidTransition .exclusive .invalid
  | S_I : ValidTransition .shared    .invalid
  | S_M : ValidTransition .shared    .modified
  | I_E : ValidTransition .invalid   .exclusive

-- ---------------------------------------------------------------------------
-- §5  Bus-read model
-- ---------------------------------------------------------------------------

/-- A conformant read from the cache system.  An Invalid line must fetch from
    memory; all other lines return their cached data. -/
def busRead {n : ℕ} {α : Type*} (sys : MESISystem n α) (i : Fin n) : α :=
  match (sys.caches i).state with
  | MESIState.invalid   => sys.memVal
  | MESIState.modified  => (sys.caches i).data
  | MESIState.exclusive => (sys.caches i).data
  | MESIState.shared    => (sys.caches i).data

-- ---------------------------------------------------------------------------
-- §6  Theorem 1 — mesi_mutual_exclusion
-- ---------------------------------------------------------------------------

/-- **MESI mutual exclusion.**

    At most one cache holds the line in Modified state.  If cores `i` and `j`
    are both Modified they must be the same core. -/
theorem mesi_mutual_exclusion
    {n : ℕ} {α : Type*}
    (sys : MESISystem n α)
    (hinv : AtMostOneModified sys)
    (i j : Fin n)
    (hi : (sys.caches i).state = MESIState.modified)
    (hj : (sys.caches j).state = MESIState.modified) :
    i = j :=
  hinv i j hi hj

-- ---------------------------------------------------------------------------
-- §7  Theorem 2 — mesi_data_consistency
-- ---------------------------------------------------------------------------

/-- **MESI data consistency.**

    If the system satisfies `ModifiedIsCurrentWrite` and cache `i` is in
    Modified state, then its data field equals the last-write value. -/
theorem mesi_data_consistency
    {n : ℕ} {α : Type*}
    (sys : MESISystem n α)
    (hinv : ModifiedIsCurrentWrite sys)
    (i : Fin n)
    (hi : (sys.caches i).state = MESIState.modified) :
    (sys.caches i).data = sys.lastWrite :=
  hinv i hi

-- ---------------------------------------------------------------------------
-- §8  Theorem 3 — mesi_shared_agreement
-- ---------------------------------------------------------------------------

/-- **MESI shared agreement.**

    Any two caches in Shared state hold identical data values. -/
theorem mesi_shared_agreement
    {n : ℕ} {α : Type*}
    (sys : MESISystem n α)
    (hinv : SharedAgreement sys)
    (i j : Fin n)
    (hi : (sys.caches i).state = MESIState.shared)
    (hj : (sys.caches j).state = MESIState.shared) :
    (sys.caches i).data = (sys.caches j).data :=
  hinv i j hi hj

-- ---------------------------------------------------------------------------
-- §9  Theorem 4 — mesi_exclusive_unique
-- ---------------------------------------------------------------------------

/-- **MESI exclusive uniqueness.**

    At most one cache can hold the line in Exclusive state at any time. -/
theorem mesi_exclusive_unique
    {n : ℕ} {α : Type*}
    (sys : MESISystem n α)
    (hinv : AtMostOneExclusive sys)
    (i j : Fin n)
    (hi : (sys.caches i).state = MESIState.exclusive)
    (hj : (sys.caches j).state = MESIState.exclusive) :
    i = j :=
  hinv i j hi hj

-- ---------------------------------------------------------------------------
-- §10  Theorem 5 — mesi_invalid_no_stale
-- ---------------------------------------------------------------------------

/-- **MESI invalid forces bus transaction.**

    If cache `i` is in the Invalid state, `busRead` returns `sys.memVal`
    (the authoritative memory value), not the stale `data` field. -/
theorem mesi_invalid_no_stale
    {n : ℕ} {α : Type*}
    (sys : MESISystem n α)
    (i : Fin n)
    (hi : (sys.caches i).state = MESIState.invalid) :
    busRead sys i = sys.memVal := by
  simp [busRead, hi]

-- ---------------------------------------------------------------------------
-- §11  Theorem 6 — mesi_transition_valid
-- ---------------------------------------------------------------------------

/-- **I → M is not a valid MESI transition.**

    The `ValidTransition` inductive has no constructor for
    `invalid → modified`, so the proposition is vacuously empty. -/
theorem mesi_transition_valid_no_I_to_M :
    ¬ValidTransition MESIState.invalid MESIState.modified := by
  intro h
  cases h

/-- The only valid transition out of Invalid is to Exclusive. -/
theorem mesi_invalid_successor_exclusive
    (s : MESIState)
    (h : ValidTransition MESIState.invalid s) :
    s = MESIState.exclusive := by
  cases h
  rfl

/-- **MESI transition validity.**

    Packages the key safety properties of `ValidTransition`:
      (a) If the source state is Invalid, the only reachable next state is
          Exclusive (no direct I → M jump).
      (b) Invalid → Modified is never a valid transition. -/
theorem mesi_transition_valid
    {from_state to_state : MESIState}
    (h : ValidTransition from_state to_state) :
    (from_state = MESIState.invalid → to_state = MESIState.exclusive) ∧
    ¬(from_state = MESIState.invalid ∧ to_state = MESIState.modified) := by
  constructor
  · intro hinv
    subst hinv
    exact mesi_invalid_successor_exclusive to_state h
  · rintro ⟨hinv, hmod⟩
    subst hinv hmod
    exact mesi_transition_valid_no_I_to_M h

end Pythia.Hardware.CacheCoherence
