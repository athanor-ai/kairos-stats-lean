import Mathlib

open Finset

-- Priority encoder: given N-bit input, returns index of highest-priority set bit.
-- Priority is from LSB (index 0 = highest priority).

noncomputable def priorityEncode (N : ℕ) (bits : Fin N → Bool) : Option (Fin N) :=
  (Finset.univ.filter (fun i : Fin N => bits i)).min

/-
The output is a valid index (when any bit is set)
-/
theorem priority_encode_valid (N : ℕ) (bits : Fin N → Bool)
    (h : ∃ i, bits i = true) :
    ∃ j, priorityEncode N bits = some j ∧ bits j = true := by
  obtain ⟨ i, hi ⟩ := h;
  have h_filter_nonempty : Finset.Nonempty (Finset.univ.filter (fun i => bits i)) := by
    exact ⟨ i, by simpa using hi ⟩;
  obtain ⟨ j, hj ⟩ := Finset.min_of_nonempty h_filter_nonempty;
  exact ⟨ j, hj, by simpa using Finset.mem_of_min hj ⟩

/-
The output is the minimum set index
-/
theorem priority_encode_is_min (N : ℕ) (bits : Fin N → Bool)
    (j : Fin N) (hj : priorityEncode N bits = some j) :
    ∀ k : Fin N, bits k = true → j ≤ k := by
  exact fun k hk ↦ Finset.min_le_of_eq ( Finset.mem_filter.mpr ⟨ Finset.mem_univ k, hk ⟩ ) hj

/-
No output when no bits set
-/
theorem priority_encode_none (N : ℕ) (bits : Fin N → Bool)
    (h : ∀ i, bits i = false) :
    priorityEncode N bits = none := by
  unfold priorityEncode; aesop;

/-
Monotonicity: setting more bits doesn't change the winner if the old winner is still set
-/
theorem priority_encode_monotone (N : ℕ) (bits1 bits2 : Fin N → Bool)
    (j : Fin N)
    (hj : priorityEncode N bits1 = some j)
    (h_superset : ∀ i, bits1 i = true → bits2 i = true) :
    ∃ k, priorityEncode N bits2 = some k ∧ k ≤ j := by
  have h_inf_le : j ∈ Finset.univ.filter (fun i => bits2 i = true) := by
    have := Finset.mem_of_min hj; aesop;
  have h_inf_le : Finset.inf (Finset.univ.filter (fun i => bits2 i = true)) WithTop.some ≤ j := by
    exact Finset.inf_le h_inf_le;
  cases h : Finset.inf ( Finset.univ.filter ( fun i => bits2 i = true ) ) WithTop.some <;> aesop

/-
Idempotence: encoding a one-hot vector returns that index
-/
theorem priority_encode_one_hot (N : ℕ) (i : Fin N) :
    priorityEncode N (fun j => decide (j = i)) = some i := by
  unfold priorityEncode;
  simp +decide [ Finset.min ];
  rw [ Finset.filter_eq' ] ; aesop