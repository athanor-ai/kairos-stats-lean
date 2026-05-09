import Mathlib

-- TLB coherence (simplified model for Aristotle v2).
-- After page table update + TLB invalidation, no stale translations.

variable {n : ℕ}

structure TLBEntry where
  vaddr : ℕ
  paddr : ℕ
  valid : Bool

def tlbInvalidate (entries : Fin n → TLBEntry) (va : ℕ) : Fin n → TLBEntry :=
  fun i => if (entries i).vaddr = va then { entries i with valid := false } else entries i

def tlbLookupFirst (entries : Fin n → TLBEntry) (va : ℕ) : Option ℕ :=
  match Finset.univ.filter (fun i : Fin n => (entries i).valid && decide ((entries i).vaddr = va)) |>.min with
  | some i => some (entries i).paddr
  | none => none

/-
After invalidating va, no valid entry maps va
-/
theorem invalidate_removes_mapping (entries : Fin n → TLBEntry) (va : ℕ) :
    ∀ i : Fin n, ((tlbInvalidate entries va) i).vaddr = va →
      ((tlbInvalidate entries va) i).valid = false := by
  unfold tlbInvalidate; aesop;

/-
Invalidation doesn't affect other mappings
-/
theorem invalidate_preserves_other (entries : Fin n → TLBEntry) (va : ℕ) :
    ∀ i : Fin n, (entries i).vaddr ≠ va →
      (tlbInvalidate entries va) i = entries i := by
  unfold tlbInvalidate; aesop;

/-
Coherence: after invalidating va and refilling with new mapping,
the refilled entry has the correct new physical address.
-/
theorem invalidate_then_refill_correct
    (entries : Fin n → TLBEntry) (va pa_new : ℕ)
    (refill_idx : Fin n) :
    (Function.update (tlbInvalidate entries va) refill_idx
      { vaddr := va, paddr := pa_new, valid := true }) refill_idx =
      { vaddr := va, paddr := pa_new, valid := true } :=
  Function.update_self refill_idx _ _