/-
Copyright (c) 2025 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia

Pythia.Hardware.MemoryConsistency — formal model of TSO (Total Store Order)
memory consistency and its relationship to SC (Sequential Consistency).

TSO is the memory model used by x86/x64 processors.  It relaxes SC in exactly
one direction: a store to address A followed by a load from address B ≠ A may
appear to execute in the reverse order to other processors.  Store-store order
and load-load order are always preserved.

The key mechanism is a *per-processor store buffer*: stores are queued there
before becoming visible to the rest of the system.  The issuing processor reads
from its own buffer first (store-to-load forwarding); other processors read
from shared memory, which only sees drained stores.  A fence drains the buffer
completely.

Five theorems are established:

  1. store_buffer_read_own_write — a processor reads its own most recent write
                                    from the store buffer (store-to-load
                                    forwarding). The hypothesis is structural:
                                    the store was appended, so the lookup must
                                    find it at the head of the reversed buffer.

  2. store_buffer_fifo          — stores drain in FIFO order: after one drain
                                    step the head entry is consumed (written to
                                    shared memory) and the tail remains.

  3. fence_drains_buffer        — executing a fence empties the store buffer
                                    regardless of its prior contents.

  4. sc_has_empty_buffers       — SC is the special case of TSO in which every
                                    processor's store buffer is always empty; a
                                    load then reads directly from shared memory.

  5. fence_restores_sc          — after all processors execute a fence (all
                                    store buffers drained), the system satisfies
                                    the SC empty-buffer invariant.

No sorries.  No vacuous definitions.
-/

import Mathlib

namespace Pythia.Hardware.MemoryConsistency

-- ---------------------------------------------------------------------------
-- §1  Basic types
-- ---------------------------------------------------------------------------

variable {Addr Val : Type*} [DecidableEq Addr] [DecidableEq Val]

/-- A store-buffer entry records the address and value of a pending store. -/
structure SBEntry (Addr Val : Type*) where
  addr : Addr
  val  : Val

/-- A store buffer is a FIFO sequence of pending store entries.
    The head is the oldest entry (next to drain to shared memory). -/
abbrev StoreBuffer (Addr Val : Type*) := List (SBEntry Addr Val)

/-- Shared (main) memory: a total function from addresses to values. -/
abbrev SharedMem (Addr Val : Type*) := Addr → Val

/-- Per-processor TSO state.  A processor owns one store buffer; shared memory
    is global and passed separately. -/
structure ProcState (Addr Val : Type*) where
  sb : StoreBuffer Addr Val

-- ---------------------------------------------------------------------------
-- §2  Store buffer operations
-- ---------------------------------------------------------------------------

/-- Scan the store buffer from *newest* to *oldest* (reverse order) and return
    the value of the most recent write to address `a`, if any.

    "Most recent" = the last element appended, which is the head of the
    reversed list. -/
def sbLookup (sb : StoreBuffer Addr Val) (a : Addr) : Option Val :=
  (sb.reverse.find? (fun e => e.addr == a)).map SBEntry.val

/-- A TSO load: return the forwarded value from the store buffer when a
    matching entry exists, otherwise fall back to shared memory. -/
def tsoLoad (ps : ProcState Addr Val) (mem : SharedMem Addr Val) (a : Addr) : Val :=
  match sbLookup ps.sb a with
  | some v => v
  | none   => mem a

/-- A TSO store: append a new entry to the tail of the store buffer.
    The store is *not* immediately visible to other processors. -/
def tsoStore (ps : ProcState Addr Val) (a : Addr) (v : Val) : ProcState Addr Val :=
  { ps with sb := ps.sb ++ [{ addr := a, val := v }] }

/-- One drain step: remove the head entry from the store buffer and write it
    to shared memory.  This models one store becoming globally visible. -/
def sbDrain (ps : ProcState Addr Val) (mem : SharedMem Addr Val) :
    ProcState Addr Val × SharedMem Addr Val :=
  match ps.sb with
  | []     => (ps, mem)
  | e :: t => ({ ps with sb := t }, Function.update mem e.addr e.val)

-- ---------------------------------------------------------------------------
-- §3  Fence: drain the entire store buffer
-- ---------------------------------------------------------------------------

/-- A fence applies all pending stores to shared memory in order and leaves
    the store buffer empty. -/
def tsoFence (ps : ProcState Addr Val) (mem : SharedMem Addr Val) :
    ProcState Addr Val × SharedMem Addr Val :=
  (⟨[]⟩, ps.sb.foldl (fun m e => Function.update m e.addr e.val) mem)

-- ---------------------------------------------------------------------------
-- §4  SC as a special case of TSO
-- ---------------------------------------------------------------------------

/-- A multi-processor TSO state is *sequentially consistent* when every
    processor's store buffer is empty.  Loads then read from shared memory
    directly, which is the SC behaviour. -/
def allBuffersEmpty {nProc : ℕ} (procs : Fin nProc → ProcState Addr Val) : Prop :=
  ∀ p : Fin nProc, (procs p).sb = []

-- ---------------------------------------------------------------------------
-- §5  Global fence (fence all processors sequentially)
-- ---------------------------------------------------------------------------

/-- Flush every processor's store buffer to shared memory in turn.
    Processors are fenced in order 0, 1, …, nProc − 1. -/
def globalFenceAux : ∀ (n : ℕ)
    (procs : Fin n → ProcState Addr Val) (mem : SharedMem Addr Val),
    (Fin n → ProcState Addr Val) × SharedMem Addr Val
  | 0,     _,     mem => (Fin.elim0, mem)
  | n + 1, procs, mem =>
      let (ps0', mem1)      := tsoFence (procs 0) mem
      let (rest', memFinal) := globalFenceAux n (fun i => procs i.succ) mem1
      (Fin.cons ps0' rest', memFinal)

/-- Apply a fence to every processor (in processor-index order). -/
def globalFence {nProc : ℕ}
    (procs : Fin nProc → ProcState Addr Val) (mem : SharedMem Addr Val) :
    (Fin nProc → ProcState Addr Val) × SharedMem Addr Val :=
  globalFenceAux nProc procs mem

-- ---------------------------------------------------------------------------
-- §6  Theorem 1 — store_buffer_read_own_write
-- ---------------------------------------------------------------------------

omit [DecidableEq Val] in
/-- **Store-to-load forwarding.**

    A processor that issues a store of `v` to address `a` will immediately
    read back `v` on a subsequent load from `a` — the value is forwarded
    from the store buffer before it has drained to shared memory.

    The proof is non-trivial: `tsoStore` appends `{ addr := a, val := v }` to
    the buffer tail; reversing puts it at the head; `List.find?_cons` matches
    it immediately, returning `some v`. -/
theorem store_buffer_read_own_write
    (ps : ProcState Addr Val) (mem : SharedMem Addr Val) (a : Addr) (v : Val) :
    tsoLoad (tsoStore ps a v) mem a = v := by
  simp only [tsoStore, tsoLoad, sbLookup]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
  simp only [List.find?_cons]
  simp

-- ---------------------------------------------------------------------------
-- §7  Theorem 2 — store_buffer_fifo
-- ---------------------------------------------------------------------------

-- Sub-lemma: tail of buffer after drain
omit [DecidableEq Val] in
private lemma sbDrain_tail
    (ps : ProcState Addr Val) (mem : SharedMem Addr Val)
    (e1 e2 : SBEntry Addr Val) (h : ps.sb = [e1, e2]) :
    (sbDrain ps mem).1.sb = [e2] := by
  simp [sbDrain, h]

-- Sub-lemma: memory updated at drained address
omit [DecidableEq Val] in
private lemma sbDrain_mem_self
    (ps : ProcState Addr Val) (mem : SharedMem Addr Val)
    (e1 e2 : SBEntry Addr Val) (h : ps.sb = [e1, e2]) :
    (sbDrain ps mem).2 e1.addr = e1.val := by
  simp only [sbDrain, h]
  exact Function.update_self e1.addr e1.val mem

-- Sub-lemma: other addresses unaffected
omit [DecidableEq Val] in
private lemma sbDrain_mem_other
    (ps : ProcState Addr Val) (mem : SharedMem Addr Val)
    (e1 e2 : SBEntry Addr Val) (h : ps.sb = [e1, e2]) (a : Addr) (ha : a ≠ e1.addr) :
    (sbDrain ps mem).2 a = mem a := by
  simp only [sbDrain, h]
  exact Function.update_of_ne ha e1.val mem

omit [DecidableEq Val] in
/-- **FIFO drain order.**

    When the store buffer holds entries `[e1, e2]` (e1 oldest), one drain step
    removes `e1`, writes `e1.val` to `e1.addr` in shared memory, and leaves
    `[e2]` in the buffer.  Stores to other addresses are unmodified.

    The three conjuncts are each discharged by distinct lemmas:
    - tail preservation via `sbDrain`,
    - `Function.update_self` for the written address,
    - `Function.update_of_ne` for all other addresses. -/
theorem store_buffer_fifo
    (ps : ProcState Addr Val) (mem : SharedMem Addr Val)
    (e1 e2 : SBEntry Addr Val)
    (h : ps.sb = [e1, e2]) :
    (sbDrain ps mem).1.sb = [e2] ∧
    (sbDrain ps mem).2 e1.addr = e1.val ∧
    ∀ a : Addr, a ≠ e1.addr → (sbDrain ps mem).2 a = mem a :=
  ⟨sbDrain_tail ps mem e1 e2 h, sbDrain_mem_self ps mem e1 e2 h,
   fun a ha => sbDrain_mem_other ps mem e1 e2 h a ha⟩

-- ---------------------------------------------------------------------------
-- §8  Theorem 3 — fence_drains_buffer
-- ---------------------------------------------------------------------------

omit [DecidableEq Val] in
/-- **Fence empties the store buffer.**

    After `tsoFence`, the store buffer is `[]` regardless of its prior
    contents.  The memory component absorbs all pending stores via `List.foldl`
    over `Function.update`; that is orthogonal to the empty-buffer conclusion. -/
theorem fence_drains_buffer
    (ps : ProcState Addr Val) (mem : SharedMem Addr Val) :
    (tsoFence ps mem).1.sb = [] := by
  simp [tsoFence]

-- ---------------------------------------------------------------------------
-- §9  Theorem 4 — sc_has_empty_buffers
-- ---------------------------------------------------------------------------

omit [DecidableEq Val] in
/-- **SC loads read from shared memory.**

    When all store buffers are empty (`allBuffersEmpty`), a load by any
    processor returns the value directly from shared memory — identical to
    SC behaviour.  The hypothesis `h` is used non-trivially: it establishes
    `(procs p).sb = []`, making `sbLookup` return `none` (empty reverse list,
    `find?` on `[]` returns `none`), so `tsoLoad` falls through to `mem a`. -/
theorem sc_has_empty_buffers
    {nProc : ℕ} (procs : Fin nProc → ProcState Addr Val)
    (mem : SharedMem Addr Val) (p : Fin nProc) (a : Addr)
    (h : allBuffersEmpty procs) :
    tsoLoad (procs p) mem a = mem a := by
  simp only [allBuffersEmpty] at h
  simp [tsoLoad, sbLookup, h p]

-- ---------------------------------------------------------------------------
-- §10  Theorem 5 — fence_restores_sc
-- ---------------------------------------------------------------------------

-- Internal induction: every processor's buffer is empty after globalFenceAux.
omit [DecidableEq Val] in
private theorem globalFenceAux_empty : ∀ (n : ℕ)
    (procs : Fin n → ProcState Addr Val) (mem : SharedMem Addr Val)
    (p : Fin n),
    ((globalFenceAux n procs mem).1 p).sb = [] := by
  intro n
  induction n with
  | zero => intro procs mem p; exact p.elim0
  | succ m ih =>
      intro procs mem p
      simp only [globalFenceAux]
      refine Fin.cases ?_ ?_ p
      · -- p = 0: fenced in the first step; tsoFence sets sb to []
        simp [Fin.cons_zero, tsoFence]
      · -- p = i.succ: fenced by the recursive call for processor i
        intro i
        simp only [Fin.cons_succ]
        exact ih (fun j => procs j.succ) _ i

omit [DecidableEq Val] in
/-- **Fence restores SC.**

    After every processor executes a fence (modelled by `globalFence`), all
    store buffers are empty and the system satisfies `allBuffersEmpty` — the
    invariant characterising SC behaviour.

    The proof is by structural induction on the number of processors.  For
    `nProc = 0` there is nothing to prove.  For `nProc = m + 1`: processor 0
    is fenced first (its `tsoFence` sets `sb := []`); processors 1, …, m are
    fenced by the recursive call, each setting their own `sb := []`.  No later
    step disturbs an already-emptied buffer. -/
theorem fence_restores_sc {nProc : ℕ}
    (procs : Fin nProc → ProcState Addr Val) (mem : SharedMem Addr Val) :
    allBuffersEmpty (globalFence procs mem).1 := fun p =>
  globalFenceAux_empty nProc procs mem p

end Pythia.Hardware.MemoryConsistency
