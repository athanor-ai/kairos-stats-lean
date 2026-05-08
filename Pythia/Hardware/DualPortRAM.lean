import Mathlib

-- Dual-port RAM correctness for MEM_2P / MEM_DP verification.
-- Two ports can read/write simultaneously. Key property:
-- no corruption when both ports access different addresses.

variable {Addr Data : Type*} [DecidableEq Addr]

def dpWrite (mem : Addr → Data) (addr : Addr) (val : Data) : Addr → Data :=
  Function.update mem addr val

-- Simultaneous writes to different addresses commute
theorem dual_write_commute (mem : Addr → Data)
    (a1 a2 : Addr) (d1 d2 : Data) (h : a1 ≠ a2) :
    dpWrite (dpWrite mem a1 d1) a2 d2 =
    dpWrite (dpWrite mem a2 d2) a1 d1 := by
  simp only [dpWrite]
  exact Function.update_comm h d1 d2 mem

-- Read from port A unaffected by write on port B to different address
theorem read_write_isolation (mem : Addr → Data)
    (r_addr w_addr : Addr) (w_data : Data) (h : r_addr ≠ w_addr) :
    dpWrite mem w_addr w_data r_addr = mem r_addr := by
  simp only [dpWrite]
  exact Function.update_of_ne h w_data mem

-- Write-then-read on same port, same address returns written value
theorem write_read_same (mem : Addr → Data) (addr : Addr) (val : Data) :
    dpWrite mem addr val addr = val := by
  simp only [dpWrite]
  exact Function.update_self addr val mem

-- Simultaneous read-read on both ports returns same value
omit [DecidableEq Addr] in
theorem dual_read_consistent (mem : Addr → Data) (addr : Addr) :
    mem addr = mem addr := rfl

-- Write doesn't affect other addresses
theorem write_other_unchanged (mem : Addr → Data)
    (w_addr r_addr : Addr) (val : Data) (h : r_addr ≠ w_addr) :
    dpWrite mem w_addr val r_addr = mem r_addr := by
  simp only [dpWrite]
  exact Function.update_of_ne h val mem
