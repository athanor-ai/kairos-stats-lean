import Mathlib

-- FIFO pointer-based occupancy invariant.
-- A circular FIFO with depth D uses write pointer wr and read pointer rd.
-- Occupancy = (wr - rd) mod D.
-- Invariant: 0 ≤ occupancy ≤ D under valid read/write operations.

structure FifoState where
  depth : ℕ
  wr : ℕ
  rd : ℕ
  h_depth_pos : 0 < depth

def occupancy (s : FifoState) : ℕ := (s.wr - s.rd) % s.depth

def fifoWrite (s : FifoState) : FifoState :=
  { s with wr := s.wr + 1 }

def fifoRead (s : FifoState) (_h : occupancy s > 0) : FifoState :=
  { s with rd := s.rd + 1 }

/-
Occupancy is always < depth
-/
theorem occupancy_lt_depth (s : FifoState) :
    occupancy s < s.depth := by
  exact Nat.mod_lt _ s.h_depth_pos

/-
Write increments occupancy by 1 (when not full and wr ≥ rd)
Note: the hypothesis wr ≥ rd is necessary because occupancy uses
natural-number subtraction (wr - rd), which truncates to 0 when rd > wr.
-/
theorem occupancy_after_write (s : FifoState)
    (hge : s.wr ≥ s.rd)
    (h : occupancy s < s.depth - 1) :
    occupancy (fifoWrite s) = occupancy s + 1 := by
  unfold fifoWrite occupancy at *;
  rw [ show s.wr + 1 - s.rd = s.wr - s.rd + 1 by omega ];
  rw [ Nat.add_mod, Nat.mod_eq_of_lt ];
  · rcases s with ⟨ _ | _ | s_depth, s_wr, s_rd, hs_depth ⟩ <;> trivial;
  · rcases k : s.depth with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ]

/-
Read decrements occupancy by 1
-/
theorem occupancy_after_read (s : FifoState) (h : occupancy s > 0) :
    occupancy (fifoRead s h) = occupancy s - 1 := by
  unfold occupancy fifoRead at *;
  cases le_total s.wr s.rd <;> simp_all +decide [ ← Nat.sub_sub ];
  rw [ ← Nat.mod_add_div ( s.wr - s.rd ) s.depth ] at *; simp_all +decide [ Nat.sub_sub ] ;
  rw [ Nat.add_comm, Nat.add_sub_assoc ];
  · norm_num [ Nat.add_mod, Nat.mod_eq_of_lt ( show ( s.wr - s.rd ) % s.depth - 1 < s.depth from lt_of_le_of_lt ( Nat.sub_le _ _ ) ( Nat.mod_lt _ s.h_depth_pos ) ) ];
  · linarith

/-
Empty FIFO has occupancy 0
-/
theorem empty_fifo_occupancy (D : ℕ) (hD : 0 < D) :
    occupancy ⟨D, 0, 0, hD⟩ = 0 := by
  exact Nat.mod_eq_zero_of_dvd ⟨ 0, by simp +decide ⟩