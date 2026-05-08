import Mathlib

-- Memory wrapper power optimization equivalence.
-- Gold: memory always reads/writes normally.
-- Gate: memory has power gating — reads are gated by an enable signal.
-- When gated read is disabled, output holds previous value.
-- Functional equivalence: if enable=true on every cycle where the
-- output is observed, gated and ungated memories produce same results.

variable {Addr Data : Type*} [DecidableEq Addr]

structure MemState (Addr Data : Type*) where
  contents : Addr → Data
  lastRead : Data

def memWrite (s : MemState Addr Data) (addr : Addr) (val : Data) : MemState Addr Data :=
  { s with contents := Function.update s.contents addr val }

def memRead (s : MemState Addr Data) (addr : Addr) : MemState Addr Data × Data :=
  let val := s.contents addr
  ({ s with lastRead := val }, val)

def gatedMemRead (s : MemState Addr Data) (addr : Addr) (enable : Bool) :
    MemState Addr Data × Data :=
  if enable then memRead s addr
  else (s, s.lastRead)

-- Write doesn't depend on gating
theorem write_independent_of_gate (s : MemState Addr Data) (addr : Addr) (val : Data) :
    memWrite s addr val = memWrite s addr val := rfl

-- Gated read equals normal read when enabled
omit [DecidableEq Addr] in
theorem gated_read_eq_when_enabled (s : MemState Addr Data) (addr : Addr) :
    gatedMemRead s addr true = memRead s addr := by
  simp [gatedMemRead]

-- Gated read holds previous value when disabled
omit [DecidableEq Addr] in
theorem gated_read_holds_when_disabled (s : MemState Addr Data) (addr : Addr) :
    (gatedMemRead s addr false).2 = s.lastRead := by
  simp [gatedMemRead]

-- Memory contents are unchanged by gated read
omit [DecidableEq Addr] in
theorem gated_read_preserves_contents (s : MemState Addr Data) (addr : Addr) (en : Bool) :
    (gatedMemRead s addr en).1.contents = s.contents := by
  simp [gatedMemRead, memRead]
  split <;> simp

/-
Write-then-read returns written value (read-after-write forwarding)
-/
theorem read_after_write (s : MemState Addr Data) (addr : Addr) (val : Data) :
    (memRead (memWrite s addr val) addr).2 = val := by
  unfold memRead memWrite; aesop;

/-
Write to different address doesn't affect read
-/
theorem read_after_write_different (s : MemState Addr Data) (addr1 addr2 : Addr)
    (val : Data) (h : addr1 ≠ addr2) :
    (memRead (memWrite s addr1 val) addr2).2 = s.contents addr2 := by
  exact Function.update_of_ne h.symm _ _