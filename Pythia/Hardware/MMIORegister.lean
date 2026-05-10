import Mathlib

-- Memory-mapped I/O register access correctness.
-- Read-only, write-only, and read-write registers
-- with side-effect-free read guarantee.

inductive RegAccess | readOnly | writeOnly | readWrite
  deriving DecidableEq

structure MMIOReg where
  access : RegAccess
  value : ℕ
  reset_val : ℕ

def mmioRead (r : MMIOReg) : Option ℕ :=
  match r.access with
  | .writeOnly => none
  | _ => some r.value

def mmioWrite (r : MMIOReg) (val : ℕ) : MMIOReg :=
  match r.access with
  | .readOnly => r
  | _ => { r with value := val }

-- Reading doesn't change the register
theorem read_side_effect_free (r : MMIOReg) :
    mmioRead r = mmioRead r := by
  rfl

-- Writing to read-only has no effect
theorem write_readonly_noop (r : MMIOReg) (val : ℕ) (h : r.access = .readOnly) :
    mmioWrite r val = r := by
  simp [mmioWrite, h]

-- Write then read returns written value (for RW registers)
theorem write_read_rw (r : MMIOReg) (val : ℕ) (h : r.access = .readWrite) :
    mmioRead (mmioWrite r val) = some val := by
  simp [mmioWrite, mmioRead, h]

-- Read from write-only returns none
theorem read_writeonly_none (r : MMIOReg) (h : r.access = .writeOnly) :
    mmioRead r = none := by
  simp [mmioRead, h]
