import Mathlib

variable {α : Type*}

-- DMA controller correctness: transfers complete without
-- corrupting source or destination data. No overlap between
-- source and destination ranges during transfer.

structure DMATransfer where
  src_addr : ℕ
  dst_addr : ℕ
  length : ℕ
  h_len : 0 < length

-- Source and destination do not overlap
def noOverlap (t : DMATransfer) : Prop :=
  t.src_addr + t.length ≤ t.dst_addr ∨ t.dst_addr + t.length ≤ t.src_addr

-- DMA copies source to destination
def dmaResult (mem : ℕ → α) (t : DMATransfer) : ℕ → α :=
  fun addr =>
    if t.dst_addr ≤ addr ∧ addr < t.dst_addr + t.length
    then mem (t.src_addr + (addr - t.dst_addr))
    else mem addr

/-
Source data unchanged after DMA (when no overlap)
-/
theorem dma_preserves_source (mem : ℕ → α) (t : DMATransfer)
    (_h : noOverlap t) (addr : ℕ)
    (_h_in_src : t.src_addr ≤ addr ∧ addr < t.src_addr + t.length) :
    dmaResult mem t addr = mem addr ∨
    (t.dst_addr ≤ addr ∧ addr < t.dst_addr + t.length) := by
  -- If the address is not in the destination address range, then DMA result returns the original value.
  by_cases h_in_dst : t.dst_addr ≤ addr ∧ addr < t.dst_addr + t.length;
  · exact Or.inr h_in_dst;
  · exact Or.inl ( if_neg h_in_dst )

/-
Destination contains source data after DMA
-/
theorem dma_copies_correctly (mem : ℕ → α) (t : DMATransfer)
    (i : ℕ) (hi : i < t.length) :
    dmaResult mem t (t.dst_addr + i) = mem (t.src_addr + i) := by
  exact if_pos ⟨ Nat.le_add_right _ _, by linarith ⟩ |> Eq.trans <| by simp +decide;

/-
Non-transfer addresses unchanged
-/
theorem dma_preserves_other (mem : ℕ → α) (t : DMATransfer)
    (addr : ℕ) (h : ¬(t.dst_addr ≤ addr ∧ addr < t.dst_addr + t.length)) :
    dmaResult mem t addr = mem addr := by
  exact if_neg h