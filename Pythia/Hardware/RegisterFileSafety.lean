import Mathlib

-- Register file safety: read-after-write correctness,
-- write port priority, and register isolation.
-- Core of any processor datapath.

variable {n : ℕ} {α : Type*} [DecidableEq (Fin n)]

def regWrite (rf : Fin n → α) (addr : Fin n) (val : α) : Fin n → α :=
  Function.update rf addr val

-- Read after write to same address returns written value
theorem read_after_write_same (rf : Fin n → α) (addr : Fin n) (val : α) :
    regWrite rf addr val addr = val := by
  simp [regWrite, Function.update_self]

-- Read after write to different address returns original
theorem read_after_write_diff (rf : Fin n → α) (a1 a2 : Fin n) (val : α) (h : a1 ≠ a2) :
    regWrite rf a1 val a2 = rf a2 := by
  simp [regWrite, Function.update_of_ne h.symm]

-- Two writes to same address: last write wins
theorem write_write_same (rf : Fin n → α) (addr : Fin n) (v1 v2 : α) :
    regWrite (regWrite rf addr v1) addr v2 = regWrite rf addr v2 := by
  simp [regWrite, Function.update_idem]

-- Two writes to different addresses commute
theorem write_write_commute (rf : Fin n → α) (a1 a2 : Fin n) (v1 v2 : α) (h : a1 ≠ a2) :
    regWrite (regWrite rf a1 v1) a2 v2 = regWrite (regWrite rf a2 v2) a1 v1 := by
  simp [regWrite, Function.update_comm h]
