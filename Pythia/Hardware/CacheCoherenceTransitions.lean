/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Hardware.CacheCoherenceTransitions

Proves that MESI state transitions PRESERVE coherence invariants.

CacheCoherence.lean establishes invariants (AtMostOneModified, SharedAgreement,
etc.) but ASSUMES they hold. This file closes that gap: it models concrete
read/write transitions and proves each one maintains the invariant.

Key results:

  1. `write_preserves_coherence`  — write transition (writer→M, others→I)
                                    preserves full Coherent invariant
                                    (unconditionally).
  2. `read_preserves_coherence`   — read transition (M→S downgrade, requester→S)
                                    preserves full Coherent invariant
                                    GIVEN that the read value is consistent
                                    with existing cached data (3 preconditions).
  3. `initial_state_coherent`     — all-Invalid initial state satisfies
                                    Coherent.
  4. `trace_preserves_modified`   — any trace of read/write ops preserves
                                    AtMostOneModified (weaker than full
                                    Coherent; full trace coherence requires
                                    threading the read consistency
                                    preconditions).

Limitation: read_preserves_coherence requires caller to prove that the
read value matches existing shared/modified/exclusive data. This is a
real protocol requirement (the bus provides the correct value), but the
theorem does not model the bus — the caller must supply this evidence.

No sorries.
-/

import Mathlib

namespace Pythia.Hardware.CacheCoherenceTransitions

-- Re-use the MESI model from CacheCoherence
inductive MESIState where
  | modified  : MESIState
  | exclusive : MESIState
  | shared    : MESIState
  | invalid   : MESIState
  deriving DecidableEq, Repr

structure CacheLine where
  state : MESIState
  data  : ℕ
  deriving DecidableEq

-- ---------------------------------------------------------------------------
-- §1  System model with concrete transitions
-- ---------------------------------------------------------------------------

structure MESISystem (n : ℕ) where
  caches : Fin n → CacheLine

def AtMostOneModified {n : ℕ} (sys : MESISystem n) : Prop :=
  ∀ i j : Fin n,
    (sys.caches i).state = .modified →
    (sys.caches j).state = .modified →
    i = j

def AtMostOneExclusive {n : ℕ} (sys : MESISystem n) : Prop :=
  ∀ i j : Fin n,
    (sys.caches i).state = .exclusive →
    (sys.caches j).state = .exclusive →
    i = j

def NoModifiedAndExclusive {n : ℕ} (sys : MESISystem n) : Prop :=
  ∀ i j : Fin n,
    ¬((sys.caches i).state = .modified ∧ (sys.caches j).state = .exclusive)

def SharedAgreement {n : ℕ} (sys : MESISystem n) : Prop :=
  ∀ i j : Fin n,
    (sys.caches i).state = .shared →
    (sys.caches j).state = .shared →
    (sys.caches i).data = (sys.caches j).data

def Coherent {n : ℕ} (sys : MESISystem n) : Prop :=
  AtMostOneModified sys ∧ AtMostOneExclusive sys ∧
  NoModifiedAndExclusive sys ∧ SharedAgreement sys

-- ---------------------------------------------------------------------------
-- §2  Write transition: writer → Modified, all others → Invalid
-- ---------------------------------------------------------------------------

def writeTransition {n : ℕ} (sys : MESISystem n) (writer : Fin n) (val : ℕ) :
    MESISystem n :=
  ⟨fun i =>
    if i = writer then ⟨.modified, val⟩
    else ⟨.invalid, (sys.caches i).data⟩⟩

-- ---------------------------------------------------------------------------
-- §3  Read transition: requester → Shared, Modified owner → Shared (writeback)
-- ---------------------------------------------------------------------------

def readTransition {n : ℕ} (sys : MESISystem n) (reader : Fin n) (val : ℕ) :
    MESISystem n :=
  ⟨fun i =>
    if i = reader then ⟨.shared, val⟩
    else match (sys.caches i).state with
      | .modified  => ⟨.shared, (sys.caches i).data⟩
      | .exclusive => ⟨.shared, (sys.caches i).data⟩
      | s          => ⟨s, (sys.caches i).data⟩⟩

-- ---------------------------------------------------------------------------
-- §4  Theorem 1 — write preserves AtMostOneModified
-- ---------------------------------------------------------------------------

theorem write_preserves_modified {n : ℕ} (sys : MESISystem n)
    (writer : Fin n) (val : ℕ) :
    AtMostOneModified (writeTransition sys writer val) := by
  intro i j hi hj
  simp only [writeTransition, AtMostOneModified] at *
  by_cases hei : i = writer <;> by_cases hej : j = writer
  · rw [hei, hej]
  · simp [hej] at hj
  · simp [hei] at hi
  · simp [hei] at hi

theorem write_preserves_exclusive {n : ℕ} (sys : MESISystem n)
    (writer : Fin n) (val : ℕ) :
    AtMostOneExclusive (writeTransition sys writer val) := by
  intro i j hi hj
  simp only [writeTransition, AtMostOneExclusive] at *
  by_cases hei : i = writer
  · simp [hei] at hi
  · simp [hei] at hi

theorem write_preserves_no_me {n : ℕ} (sys : MESISystem n)
    (writer : Fin n) (val : ℕ) :
    NoModifiedAndExclusive (writeTransition sys writer val) := by
  intro i j ⟨hi, hj⟩
  simp only [writeTransition, NoModifiedAndExclusive] at *
  by_cases hei : i = writer
  · by_cases hej : j = writer
    · simp [hej] at hj
    · simp [hej] at hj
  · simp [hei] at hi

theorem write_preserves_shared {n : ℕ} (sys : MESISystem n)
    (writer : Fin n) (val : ℕ) :
    SharedAgreement (writeTransition sys writer val) := by
  intro i j hi hj
  simp only [writeTransition, SharedAgreement] at *
  by_cases hei : i = writer
  · simp [hei] at hi
  · simp [hei] at hi

theorem write_preserves_coherence {n : ℕ} (sys : MESISystem n)
    (writer : Fin n) (val : ℕ) (h : Coherent sys) :
    Coherent (writeTransition sys writer val) :=
  ⟨write_preserves_modified sys writer val,
   write_preserves_exclusive sys writer val,
   write_preserves_no_me sys writer val,
   write_preserves_shared sys writer val⟩

-- ---------------------------------------------------------------------------
-- §5  Theorem 2 — read preserves AtMostOneModified
-- ---------------------------------------------------------------------------

theorem read_preserves_modified {n : ℕ} (sys : MESISystem n)
    (reader : Fin n) (val : ℕ) :
    AtMostOneModified (readTransition sys reader val) := by
  intro i j hi hj
  simp only [readTransition, AtMostOneModified] at *
  by_cases hei : i = reader
  · simp [hei] at hi
  · by_cases hej : j = reader
    · simp [hej] at hj
    · simp [hei] at hi
      simp [hej] at hj
      split at hi <;> simp_all

theorem read_preserves_exclusive {n : ℕ} (sys : MESISystem n)
    (reader : Fin n) (val : ℕ) :
    AtMostOneExclusive (readTransition sys reader val) := by
  intro i j hi hj
  simp only [readTransition, AtMostOneExclusive] at *
  by_cases hei : i = reader
  · simp [hei] at hi
  · simp [hei] at hi
    split at hi <;> simp_all

theorem read_preserves_no_me {n : ℕ} (sys : MESISystem n)
    (reader : Fin n) (val : ℕ) :
    NoModifiedAndExclusive (readTransition sys reader val) := by
  intro i j ⟨hi, hj⟩
  simp only [readTransition, NoModifiedAndExclusive] at *
  by_cases hei : i = reader
  · simp [hei] at hi
  · by_cases hej : j = reader
    · simp [hej] at hj
    · simp [hei] at hi
      simp [hej] at hj
      split at hi <;> simp_all

private theorem read_all_shared_have_val {n : ℕ} (sys : MESISystem n)
    (reader : Fin n) (val : ℕ)
    (h_val : ∀ i : Fin n, (sys.caches i).state = .shared → (sys.caches i).data = val)
    (h_mod_val : ∀ i : Fin n, (sys.caches i).state = .modified → (sys.caches i).data = val)
    (h_exc_val : ∀ i : Fin n, (sys.caches i).state = .exclusive → (sys.caches i).data = val)
    (i : Fin n)
    (hi : ((readTransition sys reader val).caches i).state = .shared) :
    ((readTransition sys reader val).caches i).data = val := by
  simp only [readTransition] at hi ⊢
  by_cases hei : i = reader
  · simp [hei]
  · simp [hei] at hi ⊢
    split <;> simp_all

theorem read_preserves_shared_with_consistent_data {n : ℕ} (sys : MESISystem n)
    (reader : Fin n) (val : ℕ)
    (h_sa : SharedAgreement sys)
    (h_val : ∀ i : Fin n, (sys.caches i).state = .shared → (sys.caches i).data = val)
    (h_mod_val : ∀ i : Fin n, (sys.caches i).state = .modified → (sys.caches i).data = val)
    (h_exc_val : ∀ i : Fin n, (sys.caches i).state = .exclusive → (sys.caches i).data = val) :
    SharedAgreement (readTransition sys reader val) := by
  intro i j hi hj
  have := read_all_shared_have_val sys reader val h_val h_mod_val h_exc_val i hi
  have := read_all_shared_have_val sys reader val h_val h_mod_val h_exc_val j hj
  simp_all

theorem read_preserves_coherence {n : ℕ} (sys : MESISystem n)
    (reader : Fin n) (val : ℕ) (h : Coherent sys)
    (h_val : ∀ i : Fin n, (sys.caches i).state = .shared → (sys.caches i).data = val)
    (h_mod_val : ∀ i : Fin n, (sys.caches i).state = .modified → (sys.caches i).data = val)
    (h_exc_val : ∀ i : Fin n, (sys.caches i).state = .exclusive → (sys.caches i).data = val) :
    Coherent (readTransition sys reader val) :=
  ⟨read_preserves_modified sys reader val,
   read_preserves_exclusive sys reader val,
   read_preserves_no_me sys reader val,
   read_preserves_shared_with_consistent_data sys reader val h.2.2.2 h_val h_mod_val h_exc_val⟩

-- ---------------------------------------------------------------------------
-- §6  Theorem 3 — initial state is coherent
-- ---------------------------------------------------------------------------

theorem initial_state_coherent (n : ℕ) :
    Coherent (⟨fun _ => ⟨MESIState.invalid, 0⟩⟩ : MESISystem n) := by
  exact ⟨
    fun i _ hi => by simp at hi,
    fun i _ hi => by simp at hi,
    fun i _ ⟨hi, _⟩ => by simp at hi,
    fun i _ hi => by simp at hi⟩

-- ---------------------------------------------------------------------------
-- §7  Theorem 6 — inductive coherence over traces
-- ---------------------------------------------------------------------------

inductive CacheOp (n : ℕ) where
  | write (core : Fin n) (val : ℕ)
  | read  (core : Fin n) (val : ℕ)

def applyOp {n : ℕ} (sys : MESISystem n) : CacheOp n → MESISystem n
  | .write core val => writeTransition sys core val
  | .read core val  => readTransition sys core val

def applyTrace {n : ℕ} (sys : MESISystem n) : List (CacheOp n) → MESISystem n
  | []        => sys
  | op :: ops => applyTrace (applyOp sys op) ops

theorem trace_preserves_modified {n : ℕ} (sys : MESISystem n)
    (ops : List (CacheOp n))
    (h_init : AtMostOneModified sys) :
    AtMostOneModified (applyTrace sys ops) := by
  induction ops generalizing sys with
  | nil => exact h_init
  | cons op ops ih =>
    apply ih
    cases op with
    | write core val => exact write_preserves_modified sys core val
    | read core val => exact read_preserves_modified sys core val

end Pythia.Hardware.CacheCoherenceTransitions
