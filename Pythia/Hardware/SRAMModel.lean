import Mathlib

-- SRAM behavioral model correctness.
-- Single-port SRAM: read and write cannot happen simultaneously.
-- Backs the MEM_1P verification pattern.

variable {n : ℕ} {α : Type*} [Inhabited α]

@[ext]
structure SRAMState (n : ℕ) (α : Type*) where
  mem : Fin n → α

def sramWrite (s : SRAMState n α) (addr : Fin n) (val : α) : SRAMState n α :=
  { mem := Function.update s.mem addr val }

def sramRead (s : SRAMState n α) (addr : Fin n) : α :=
  s.mem addr

-- Write then read same address
omit [Inhabited α] in
theorem sram_write_read_same (s : SRAMState n α) (addr : Fin n) (val : α) :
    sramRead (sramWrite s addr val) addr = val := by
  simp [sramRead, sramWrite, Function.update_self]

-- Write then read different address
omit [Inhabited α] in
theorem sram_write_read_diff (s : SRAMState n α) (a1 a2 : Fin n) (val : α) (h : a1 ≠ a2) :
    sramRead (sramWrite s a1 val) a2 = sramRead s a2 := by
  simp [sramRead, sramWrite, Function.update_of_ne h.symm]

-- Two writes same address: last wins
omit [Inhabited α] in
theorem sram_write_write_same (s : SRAMState n α) (addr : Fin n) (v1 v2 : α) :
    sramWrite (sramWrite s addr v1) addr v2 = sramWrite s addr v2 := by
  ext; simp [sramWrite, Function.update_idem]
