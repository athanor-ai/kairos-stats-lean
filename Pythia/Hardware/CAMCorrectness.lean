import Mathlib

open Finset

-- Content-Addressable Memory (CAM) correctness.
-- AP_CAM_COMPARE_US is in qa's sweep. CAM does parallel lookup:
-- given a search key, returns the index of the matching entry.

variable {n : ℕ} {Key : Type*} [DecidableEq Key]

structure CAMState (n : ℕ) (Key : Type*) where
  entries : Fin n → Key
  valid   : Fin n → Bool

def camLookup (s : CAMState n Key) (search : Key) : Option (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => s.valid i && decide (s.entries i = search))).min

def camWrite (s : CAMState n Key) (idx : Fin n) (key : Key) : CAMState n Key :=
  { entries := Function.update s.entries idx key,
    valid := Function.update s.valid idx true }

def camInvalidate (s : CAMState n Key) (idx : Fin n) : CAMState n Key :=
  { s with valid := Function.update s.valid idx false }

/-
Lookup finds a valid matching entry
-/
theorem cam_lookup_valid (s : CAMState n Key) (search : Key) (idx : Fin n)
    (h : camLookup s search = some idx) :
    s.valid idx = true ∧ s.entries idx = search := by
  have := Finset.mem_of_min h; aesop

/-
Write then lookup returns the written index (if no earlier valid match)
-/
theorem cam_write_then_lookup (s : CAMState n Key) (idx : Fin n) (key : Key)
    (h_no_earlier : ∀ j : Fin n, j < idx → ¬(s.valid j = true ∧ s.entries j = key)) :
    camLookup (camWrite s idx key) key = some idx ∨
    ∃ j, j < idx ∧ camLookup (camWrite s idx key) key = some j := by
  by_cases h' : camLookup (camWrite s idx key) key = none
  · have h_filter_empty : Finset.filter (fun j => (Function.update s.valid idx true j) &&
        (Function.update s.entries idx key j = key)) Finset.univ = ∅ := by
      unfold camLookup camWrite at h'
      exact Finset.min_eq_top.mp h'
    simp_all +decide [Finset.ext_iff, Function.update_apply]
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp h'
    by_cases h : j = idx <;> simp_all +decide [camLookup]
    have := Finset.mem_of_min hj; simp_all +decide [camWrite]
    contrapose! h_no_earlier
    exact absurd (Finset.min_le_of_eq (Finset.mem_filter.mpr ⟨Finset.mem_univ idx,
      by simp +decide⟩) hj)
      (by simp +decide; exact lt_of_le_of_ne h_no_earlier (Ne.symm h))

/-
Invalidated entry is not found by lookup
-/
theorem cam_invalidate_not_found (s : CAMState n Key) (idx : Fin n) (search : Key)
    (h_unique : ∀ j : Fin n, s.valid j = true → s.entries j = search → j = idx) :
    camLookup (camInvalidate s idx) search = none := by
  unfold camLookup
  simp +decide [Finset.min, camInvalidate]
  simp +decide [WithTop.none_eq_top]
  intro j hj hj'; specialize h_unique j
  by_cases h : j = idx <;> simp_all +decide [Function.update_apply]

/-
Lookup returns minimum matching index (priority)
-/
theorem cam_lookup_is_min (s : CAMState n Key) (search : Key) (idx : Fin n)
    (h : camLookup s search = some idx) :
    ∀ j : Fin n, s.valid j = true → s.entries j = search → idx ≤ j := by
  intro j hj_valid hj_entry
  have h_filter : j ∈ Finset.univ.filter (fun i => s.valid i && decide (s.entries i = search)) := by
    grind
  have h_min : idx ∈ Finset.univ.filter (fun i => s.valid i && decide (s.entries i = search)) ∧
      ∀ k ∈ Finset.univ.filter (fun i => s.valid i && decide (s.entries i = search)), idx ≤ k := by
    exact ⟨Finset.mem_of_min h, fun k hk => Finset.min_le_of_eq hk h⟩
  exact h_min.2 j h_filter
