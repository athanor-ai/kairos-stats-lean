/-
Copyright (c) 2025 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Pythia.Hardware.TimingAndRenaming — timing closure preservation and register
renaming correctness for hardware design.

Two independent hardware properties are established in this file.

**Part I — Timing Closure Preservation**

A combinational circuit is modelled as a list of path delays (one entry per
source-to-sink path).  Gate removal (a common synthesis optimisation) cannot
lengthen critical paths; it can only shorten or maintain them.

  1. `gate_removal_delay_le`         — removing a gate does not increase the
                                       maximum path delay (the critical path).
  2. `optimization_preserves_timing` — if the original circuit meets a timing
                                       constraint T, and the optimisation only
                                       removes/merges gates, the optimised
                                       circuit also meets T.
  3. `parallel_path_delay_max`       — the effective delay of two parallel
                                       paths is the maximum of their individual
                                       delays.

**Part II — Register Renaming Correctness**

Physical register renaming is modelled with architectural registers
`Fin n → α`, physical registers `Fin m → α`, and a rename map `Fin n → Fin m`.

  4. `rename_read_correct`                   — reading an architectural
                                               register through the rename map
                                               gives the value last written to
                                               it.
  5. `rename_write_preserves_others`         — writing to one architectural
                                               register does not affect other
                                               architectural registers' values
                                               seen through the rename map,
                                               provided they map to distinct
                                               physical registers.
  6. `rename_map_injective_safety`           — an injective rename map
                                               guarantees that no two
                                               architectural registers alias
                                               the same physical register.

No sorries anywhere.
-/

import Mathlib

namespace Pythia.Hardware.TimingAndRenaming

-- ===========================================================================
-- Part I — Timing Closure Preservation
-- ===========================================================================

-- ---------------------------------------------------------------------------
-- §1  Circuit model and critical-path delay
-- ---------------------------------------------------------------------------

-- A combinational circuit is abstracted as a finite list of path delays,
-- one entry per source-to-sink combinational path.  Delays are non-negative
-- rationals representing (e.g.) nanoseconds.
--
-- Gate removal can only eliminate paths or shorten their delays; it cannot
-- introduce new paths or increase existing delays.  We model this relationship
-- via a `GateRemovalRef` structure below.

/-- `criticalPath delays` is the maximum path delay, i.e. the clock-period
    lower bound imposed by the circuit.  Returns 0 for an empty path list
    (no combinational paths — trivially meets any non-negative constraint). -/
def criticalPath (delays : List ℚ) : ℚ :=
  delays.foldr max 0

@[simp]
lemma criticalPath_nil : criticalPath [] = 0 := rfl

-- ---------------------------------------------------------------------------
-- §2  Supporting lemmas about criticalPath
-- ---------------------------------------------------------------------------

/-- The critical-path delay is always non-negative. -/
lemma criticalPath_nonneg (delays : List ℚ) : 0 ≤ criticalPath delays := by
  induction delays with
  | nil => simp [criticalPath]
  | cons h t ih =>
    simp only [criticalPath, List.foldr_cons]
    exact ih.trans (le_max_right _ _)

/-- Every member of the delay list is at most the critical-path delay. -/
lemma mem_le_criticalPath (l : List ℚ) (d : ℚ) (hd : d ∈ l) :
    d ≤ criticalPath l := by
  induction l with
  | nil => simp at hd
  | cons h t ih =>
    simp only [List.mem_cons] at hd
    simp only [criticalPath, List.foldr_cons]
    cases hd with
    | inl heq => subst heq; exact le_max_left _ _
    | inr hmem => exact (ih hmem).trans (le_max_right _ _)

/-- Every path delay in the list (addressed by its index) is at most the
    critical-path delay. -/
lemma criticalPath_get_le (delays : List ℚ) (k : Fin delays.length) :
    delays.get k ≤ criticalPath delays :=
  mem_le_criticalPath delays (delays.get k) (List.get_mem delays k)

-- ---------------------------------------------------------------------------
-- §3  Gate-removal refinement
-- ---------------------------------------------------------------------------

/-- `GateRemovalRef A B` witnesses that circuit `B` is obtained from circuit
    `A` by gate removal:

    * Every path in `B` corresponds (injectively) to some path in `A`.
    * The delay of each `B`-path is at most the delay of the matching `A`-path
      (gate removal can only shorten or preserve individual path delays).

    Injectivity of `embed` ensures that distinct paths in `B` come from
    distinct paths in `A` — no aliasing. -/
structure GateRemovalRef (A B : List ℚ) where
  /-- Embedding of `B`-path indices into `A`-path indices. -/
  embed     : Fin B.length → Fin A.length
  embed_inj : Function.Injective embed
  /-- Each `B`-path delay is bounded by the matching `A`-path delay. -/
  delay_le  : ∀ (k : Fin B.length), B.get k ≤ A.get (embed k)

-- ---------------------------------------------------------------------------
-- §4  Theorem 1 — gate_removal_delay_le
-- ---------------------------------------------------------------------------

/-- **Theorem 1 — Gate Removal Does Not Increase Critical-Path Delay.**

    If `B` is obtained from `A` by gate removal (`GateRemovalRef A B`), then
    `criticalPath B ≤ criticalPath A`.

    Proof by induction on `B`: the `criticalPath` of a `cons`-list is
    `max h (criticalPath t)`, and each component is bounded using the embedding
    and the transitivity of ≤ through `criticalPath_get_le`. -/
theorem gate_removal_delay_le
    (A B : List ℚ) (ref : GateRemovalRef A B) :
    criticalPath B ≤ criticalPath A := by
  induction B with
  | nil =>
    simp [criticalPath]
    exact criticalPath_nonneg A
  | cons h t ih =>
    simp only [criticalPath, List.foldr_cons]
    apply max_le
    · -- Head path: h = (h :: t).get 0 ≤ A.get (embed 0) ≤ criticalPath A
      have hle := ref.delay_le ⟨0, Nat.succ_pos _⟩
      simp only [List.get] at hle
      exact hle.trans (criticalPath_get_le A (ref.embed ⟨0, Nat.succ_pos _⟩))
    · -- Tail: restrict the GateRemovalRef to the tail
      apply ih
      exact {
        embed     := fun k => ref.embed ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
        embed_inj := by
          intro a b hab
          have hinj := ref.embed_inj hab
          simp only [Fin.mk.injEq] at hinj
          exact Fin.ext (Nat.succ_injective hinj)
        delay_le  := by
          intro k
          have := ref.delay_le ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
          simp only [List.get] at this ⊢
          exact this
      }

-- ---------------------------------------------------------------------------
-- §5  Theorem 2 — optimization_preserves_timing
-- ---------------------------------------------------------------------------

/-- **Theorem 2 — Optimisation Preserves Timing Closure.**

    If the original circuit `A` meets a timing constraint `T`
    (`criticalPath A ≤ T`) and `B` is obtained from `A` by gate removal, then
    `B` also meets `T`. -/
theorem optimization_preserves_timing
    (A B : List ℚ) (T : ℚ)
    (hA : criticalPath A ≤ T)
    (ref : GateRemovalRef A B) :
    criticalPath B ≤ T :=
  (gate_removal_delay_le A B ref).trans hA

-- ---------------------------------------------------------------------------
-- §6  Theorem 3 — parallel_path_delay_max
-- ---------------------------------------------------------------------------

/-- **Theorem 3 — Parallel-Path Delay is the Maximum.**

    When two signal paths run in parallel between the same endpoints, the
    effective delay of the combined path bundle is the maximum of the two
    individual delays.  Requires both delays to be non-negative (physical
    delays are always ≥ 0). -/
theorem parallel_path_delay_max (d₁ d₂ : ℚ) (h₂ : 0 ≤ d₂) :
    criticalPath [d₁, d₂] = max d₁ d₂ := by
  simp only [criticalPath, List.foldr_cons, List.foldr_nil]
  -- criticalPath [d₁, d₂] = max d₁ (max d₂ 0) = max d₁ d₂  (using d₂ ≥ 0)
  conv_lhs => rw [max_eq_left h₂]

-- ===========================================================================
-- Part II — Register Renaming Correctness
-- ===========================================================================

-- ---------------------------------------------------------------------------
-- §7  Register file types
-- ---------------------------------------------------------------------------

variable {α : Type*}

/-- An architectural register file with `n` registers. -/
abbrev ArchRegs (n : ℕ) (α : Type*) := Fin n → α

/-- A physical register file with `m` registers. -/
abbrev PhysRegs (m : ℕ) (α : Type*) := Fin m → α

/-- A rename map: each architectural register index maps to a physical
    register index. -/
abbrev RenameMap (n m : ℕ) := Fin n → Fin m

-- ---------------------------------------------------------------------------
-- §8  Read / write primitives
-- ---------------------------------------------------------------------------

/-- Read physical register `p` from the physical file. -/
@[inline]
def physRead {m : ℕ} (prf : PhysRegs m α) (p : Fin m) : α := prf p

/-- Write value `v` to physical register `p`. -/
def physWrite {m : ℕ} (prf : PhysRegs m α) (p : Fin m) (v : α) : PhysRegs m α :=
  Function.update prf p v

/-- Read architectural register `r` through the rename map: looks up the
    physical register that `r` is currently mapped to, then reads that. -/
def archRead {n m : ℕ} (prf : PhysRegs m α) (rmap : RenameMap n m)
    (r : Fin n) : α :=
  physRead prf (rmap r)

/-- Write `v` to architectural register `r` through the rename map: writes
    to the physical register that `r` is currently mapped to. -/
def archWrite {n m : ℕ} (prf : PhysRegs m α) (rmap : RenameMap n m)
    (r : Fin n) (v : α) : PhysRegs m α :=
  physWrite prf (rmap r) v

-- ---------------------------------------------------------------------------
-- §9  Theorem 4 — rename_read_correct
-- ---------------------------------------------------------------------------

/-- **Theorem 4 — Rename Read Correct.**

    Writing value `v` to architectural register `r` through the rename map,
    then reading architectural register `r` through the same rename map,
    returns `v`. -/
theorem rename_read_correct
    {n m : ℕ} (prf : PhysRegs m α) (rmap : RenameMap n m)
    (r : Fin n) (v : α) :
    archRead (archWrite prf rmap r v) rmap r = v := by
  simp [archRead, archWrite, physRead, physWrite, Function.update_self]

-- ---------------------------------------------------------------------------
-- §10  Theorem 5 — rename_write_preserves_others
-- ---------------------------------------------------------------------------

/-- **Theorem 5 — Rename Write Preserves Other Architectural Registers.**

    Writing value `v` to architectural register `r` through the rename map
    does not affect the value seen when reading a different architectural
    register `s`, provided `r` and `s` map to *distinct* physical registers
    (`rmap r ≠ rmap s`).

    This is the fundamental non-interference property: each write is contained
    to exactly one physical register slot. -/
theorem rename_write_preserves_others
    {n m : ℕ} (prf : PhysRegs m α) (rmap : RenameMap n m)
    (r s : Fin n) (v : α)
    (hne : rmap r ≠ rmap s) :
    archRead (archWrite prf rmap r v) rmap s = archRead prf rmap s := by
  simp only [archRead, archWrite, physRead, physWrite]
  -- Function.update_of_ne : a ≠ a' → update f a' v a = f a
  -- Here a = rmap s, a' = rmap r; we need rmap s ≠ rmap r.
  exact Function.update_of_ne (Ne.symm hne) v prf

-- ---------------------------------------------------------------------------
-- §11  Theorem 6 — rename_map_injective_safety
-- ---------------------------------------------------------------------------

/-- **Theorem 6 — Injective Rename Map Guarantees No Aliasing.**

    If the rename map is injective (i.e. no two architectural registers are
    currently mapped to the same physical register — as maintained by the ROB
    free-list allocator), then distinct architectural registers are guaranteed
    to have distinct physical register mappings.  This rules out aliasing
    between any pair of distinct architectural registers. -/
theorem rename_map_injective_safety
    {n m : ℕ} (rmap : RenameMap n m)
    (hinj : Function.Injective rmap)
    (r s : Fin n) (hrs : r ≠ s) :
    rmap r ≠ rmap s :=
  fun heq => hrs (hinj heq)

/-- **Corollary** — Under an injective rename map, a write to architectural
    register `r` never aliases with any other architectural register `s ≠ r`,
    so the read-value of `s` is unchanged. -/
theorem rename_write_preserves_others_injective
    {n m : ℕ} (prf : PhysRegs m α) (rmap : RenameMap n m)
    (hinj : Function.Injective rmap)
    (r s : Fin n) (v : α) (hrs : r ≠ s) :
    archRead (archWrite prf rmap r v) rmap s = archRead prf rmap s :=
  rename_write_preserves_others prf rmap r s v
    (rename_map_injective_safety rmap hinj r s hrs)

end Pythia.Hardware.TimingAndRenaming
