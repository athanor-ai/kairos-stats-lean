/-
Copyright (c) 2025 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia

Pythia.Hardware.PipelineHazard — pipeline hazard detection and forwarding
correctness for 5-stage pipelined CPUs.

Models a canonical 5-stage pipeline (IF → ID → EX → MEM → WB) with a
register file.  Four theorems are established:

  1. forwarding_correct         — forwarding from EX/MEM/WB produces the
                                   same value as reading after write-back.
  2. no_hazard_no_forward       — when no RAW dependency exists, forwarding
                                   degenerates to a plain register read.
  3. stall_preserves_correctness — stalling on a load-use hazard produces
                                   the correct architectural result.
  4. forwarding_eliminates_stall — forwarding and stall-based resolution
                                   yield identical results; forwarding needs
                                   zero extra stall cycles.

The register file is `Fin n → α`; pipeline stages are records.  No sorries.
-/

import Mathlib

namespace Pythia.Hardware.PipelineHazard

-- ---------------------------------------------------------------------------
-- §1  Register file
-- ---------------------------------------------------------------------------

/-- A register file with `n` architectural registers holding values of type
    `α`. -/
abbrev RegFile (n : ℕ) (α : Type*) := Fin n → α

/-- Write a value to register `r` in the register file. -/
def rfWrite {n : ℕ} {α : Type*} (rf : RegFile n α) (r : Fin n) (v : α) :
    RegFile n α :=
  Function.update rf r v

/-- Read a register from the register file. -/
@[inline]
def rfRead {n : ℕ} {α : Type*} (rf : RegFile n α) (r : Fin n) : α := rf r

-- ---------------------------------------------------------------------------
-- §2  Pipeline stage records
-- ---------------------------------------------------------------------------

/-- Which pipeline stage a value is currently in. -/
inductive Stage where
  | IF  : Stage   -- Instruction Fetch
  | ID  : Stage   -- Instruction Decode / Register Read
  | EX  : Stage   -- Execute
  | MEM : Stage   -- Memory Access
  | WB  : Stage   -- Write-Back

/-- The state of a single instruction flowing through the pipeline.
    `dst` is the destination register; `val` is the computed value (available
    from EX onward); `valid` indicates whether the slot holds a live
    instruction. -/
structure PipeSlot (n : ℕ) (α : Type*) where
  dst   : Fin n        -- destination register
  val   : α            -- computed / forwarded value
  valid : Bool         -- is this slot occupied?

/-- A five-stage pipeline snapshot. -/
structure Pipeline (n : ℕ) (α : Type*) where
  rf    : RegFile n α      -- committed register file
  exSlot  : PipeSlot n α   -- EX  stage slot
  memSlot : PipeSlot n α   -- MEM stage slot
  wbSlot  : PipeSlot n α   -- WB  stage slot

-- ---------------------------------------------------------------------------
-- §3  RAW hazard detection
-- ---------------------------------------------------------------------------

/-- A RAW (Read-After-Write) hazard exists if the requesting source register
    `src` matches a destination register in a live pipeline slot. -/
def rawHazard {n : ℕ} {α : Type*} (src : Fin n) (slot : PipeSlot n α) : Prop :=
  slot.valid = true ∧ slot.dst = src

instance {n : ℕ} {α : Type*} (src : Fin n) (slot : PipeSlot n α) :
    Decidable (rawHazard src slot) :=
  instDecidableAnd

-- ---------------------------------------------------------------------------
-- §4  Forwarding unit
-- ---------------------------------------------------------------------------

/-- The forwarding unit selects the most recent in-flight value for source
    register `src`.  Priority: EX > MEM > WB > committed RF.

    This is the standard "nearest-writer wins" forwarding MUX. -/
def forwardRead {n : ℕ} {α : Type*}
    (p : Pipeline n α) (src : Fin n) : α :=
  if p.exSlot.valid = true ∧ p.exSlot.dst = src then
    p.exSlot.val
  else if p.memSlot.valid = true ∧ p.memSlot.dst = src then
    p.memSlot.val
  else if p.wbSlot.valid = true ∧ p.wbSlot.dst = src then
    p.wbSlot.val
  else
    rfRead p.rf src

/-- `commitSlot` models write-back: apply a pipeline slot's write to the
    committed register file. -/
def commitSlot {n : ℕ} {α : Type*}
    (rf : RegFile n α) (slot : PipeSlot n α) : RegFile n α :=
  if slot.valid then rfWrite rf slot.dst slot.val else rf

-- ---------------------------------------------------------------------------
-- §5  Theorem 1 — forwarding_correct
-- ---------------------------------------------------------------------------

/-- **Forwarding correctness.**

    Suppose the EX stage holds a live write to register `src` (a RAW hazard).
    Then the forwarding unit returns the same value that a plain register read
    would return *after* the write-back of the EX slot completes. -/
theorem forwarding_correct
    {n : ℕ} {α : Type*}
    (p : Pipeline n α) (src : Fin n)
    (h_valid : p.exSlot.valid = true)
    (h_dst   : p.exSlot.dst = src) :
    forwardRead p src =
      rfRead (commitSlot p.rf p.exSlot) src := by
  -- The forwarding unit takes the EX branch.
  simp only [forwardRead, h_valid, h_dst, and_self, ↓reduceIte]
  -- After write-back the committed RF has the EX value at `src`.
  simp only [commitSlot, h_valid, ↓reduceIte, rfWrite, rfRead]
  -- The update at `p.exSlot.dst` read back at `src = p.exSlot.dst`.
  rw [← h_dst]
  exact (Function.update_self p.exSlot.dst p.exSlot.val p.rf).symm

-- ---------------------------------------------------------------------------
-- §6  Theorem 2 — no_hazard_no_forward
-- ---------------------------------------------------------------------------

/-- **No-hazard, no-forwarding.**

    When no in-flight slot is writing to `src`, the forwarding unit returns
    the committed register file value — identical to a plain register read. -/
theorem no_hazard_no_forward
    {n : ℕ} {α : Type*}
    (p : Pipeline n α) (src : Fin n)
    (h_ex  : ¬rawHazard src p.exSlot)
    (h_mem : ¬rawHazard src p.memSlot)
    (h_wb  : ¬rawHazard src p.wbSlot) :
    forwardRead p src = rfRead p.rf src := by
  simp only [rawHazard, not_and] at h_ex h_mem h_wb
  simp only [forwardRead]
  -- Eliminate the EX branch.
  have hEx : ¬(p.exSlot.valid = true ∧ p.exSlot.dst = src) := by
    intro ⟨hv, hd⟩; exact absurd hd (h_ex hv)
  simp only [hEx, ↓reduceIte]
  -- Eliminate the MEM branch.
  have hMem : ¬(p.memSlot.valid = true ∧ p.memSlot.dst = src) := by
    intro ⟨hv, hd⟩; exact absurd hd (h_mem hv)
  simp only [hMem, ↓reduceIte]
  -- Eliminate the WB branch.
  have hWb : ¬(p.wbSlot.valid = true ∧ p.wbSlot.dst = src) := by
    intro ⟨hv, hd⟩; exact absurd hd (h_wb hv)
  simp only [hWb, ↓reduceIte]

-- ---------------------------------------------------------------------------
-- §7  Stall model
-- ---------------------------------------------------------------------------

/-- A load-use hazard cannot be resolved by forwarding because the loaded
    value is not available until after the MEM stage.  We model stalling as
    inserting a bubble (an invalid slot) in the EX stage and replaying the
    decode of the dependent instruction one cycle later.

    `stalledRF` applies the MEM write-back that occurs during the stall
    cycle, making the loaded value visible in the committed RF. -/
def stalledRF {n : ℕ} {α : Type*}
    (p : Pipeline n α) : RegFile n α :=
  commitSlot p.rf p.memSlot

/-- After a stall, the EX slot becomes a bubble (invalid). -/
def stalledPipeline {n : ℕ} {α : Type*}
    (p : Pipeline n α) (dummy : α) : Pipeline n α :=
  { p with
    exSlot  := { dst := p.exSlot.dst, val := dummy, valid := false }
    memSlot := p.exSlot
    wbSlot  := p.memSlot
    rf      := stalledRF p }

-- ---------------------------------------------------------------------------
-- §8  Theorem 3 — stall_preserves_correctness
-- ---------------------------------------------------------------------------

/-- **Stall preserves correctness.**

    Suppose the MEM slot holds a live load to register `src` (a load-use
    hazard that cannot be forwarded from EX).  After inserting a stall bubble
    the register file in the stalled pipeline contains the loaded value, and a
    plain register read in the stalled state equals the MEM value — the same
    result the programmer expects. -/
theorem stall_preserves_correctness
    {n : ℕ} {α : Type*}
    (p : Pipeline n α) (src : Fin n) (dummy : α)
    (h_mem_valid : p.memSlot.valid = true)
    (h_mem_dst   : p.memSlot.dst = src) :
    rfRead (stalledPipeline p dummy).rf src = p.memSlot.val := by
  simp only [stalledPipeline, stalledRF, commitSlot, h_mem_valid, ↓reduceIte,
    rfWrite, rfRead]
  rw [← h_mem_dst]
  exact Function.update_self p.memSlot.dst p.memSlot.val p.rf

-- ---------------------------------------------------------------------------
-- §9  Theorem 4 — forwarding_eliminates_stall
-- ---------------------------------------------------------------------------

/-- **Forwarding eliminates the stall.**

    Suppose the MEM slot holds a live write to `src` *and* the EX slot has
    no conflicting write to `src`.  Then:

      · forwarding reads `p.memSlot.val` directly (no stall), and
      · the stall-based resolution also reads `p.memSlot.val` (after
        the stall advances MEM to WB and commits).

    Hence both mechanisms produce the same architectural result; forwarding
    achieves this without injecting a bubble cycle. -/
theorem forwarding_eliminates_stall
    {n : ℕ} {α : Type*}
    (p : Pipeline n α) (src : Fin n) (dummy : α)
    -- MEM has a live write to src (the hazard)
    (h_mem_valid : p.memSlot.valid = true)
    (h_mem_dst   : p.memSlot.dst = src)
    -- EX does NOT have a conflicting write to src (no closer writer)
    (h_ex_no_hit : ¬(p.exSlot.valid = true ∧ p.exSlot.dst = src)) :
    -- Forwarding result equals stall-based result
    forwardRead p src =
      rfRead (stalledPipeline p dummy).rf src := by
  -- LHS: forwarding selects MEM value (EX branch disabled).
  simp only [forwardRead, h_ex_no_hit, ↓reduceIte,
    h_mem_valid, h_mem_dst, and_self]
  -- RHS: after stall, the committed RF holds the MEM value.
  simp only [stalledPipeline, stalledRF, commitSlot, h_mem_valid, ↓reduceIte,
    rfWrite, rfRead]
  rw [← h_mem_dst]
  exact (Function.update_self p.memSlot.dst p.memSlot.val p.rf).symm

end Pythia.Hardware.PipelineHazard
