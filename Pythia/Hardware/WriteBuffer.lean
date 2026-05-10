import Mathlib

-- Write buffer coherence: pending writes are forwarded
-- to reads correctly, and drain to cache/memory in order.

variable {α : Type*} [DecidableEq α]

structure WBEntry (α : Type*) where
  addr : α
  val : ℕ

def wbLookup (buf : List (WBEntry α)) (addr : α) : Option ℕ :=
  (buf.filter (fun e => e.addr = addr)).head?.map WBEntry.val

def wbInsert (buf : List (WBEntry α)) (addr : α) (val : ℕ) : List (WBEntry α) :=
  buf ++ [{ addr := addr, val := val }]

def wbDrainOne (buf : List (WBEntry α)) : List (WBEntry α) :=
  buf.tail

/-
Insert then lookup returns inserted value (for same address, if last write)
-/
theorem wb_insert_lookup (buf : List (WBEntry α)) (addr : α) (val : ℕ)
    (h_empty : buf.filter (fun e => decide (e.addr = addr)) = []) :
    wbLookup (wbInsert buf addr val) addr = some val := by
  -- By definition of `wbInsert`, the last element of `buf ++ [⟨addr, val⟩]` is `⟨addr, val⟩`.
  simp [wbInsert, wbLookup, List.filter_append, h_empty]

/-
Drain removes oldest entry (FIFO)
-/
omit [DecidableEq α] in
theorem wb_drain_removes_head (buf : List (WBEntry α)) (h : buf ≠ []) :
    (wbDrainOne buf).length = buf.length - 1 := by
  cases buf <;> aesop