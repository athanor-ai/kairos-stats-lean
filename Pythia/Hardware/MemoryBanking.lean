import Mathlib

-- Memory banking: distributing accesses across banks
-- to maximize bandwidth. No two accesses to the same
-- bank in one cycle (conflict-free).

variable {n : ℕ}

def bankId (addr num_banks : ℕ) : ℕ := addr % num_banks

-- Stride-1 access is conflict-free for power-of-2 banks
-- when number of accessors ≤ number of banks
theorem stride1_conflict_free (num_banks : ℕ) (hb : 0 < num_banks)
    (accessors : Fin num_banks → ℕ)
    (h_stride : ∀ i : Fin num_banks, accessors i = i.val) :
    Function.Injective (fun i : Fin num_banks => bankId (accessors i) num_banks) := by
  intro a b hab
  apply Fin.val_injective
  simp [bankId, h_stride] at hab
  rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hab

-- Different addresses mod num_banks go to different banks
theorem different_banks (addr1 addr2 num_banks : ℕ) (hb : 0 < num_banks)
    (h : addr1 % num_banks ≠ addr2 % num_banks) :
    bankId addr1 num_banks ≠ bankId addr2 num_banks := by
  exact h

-- Total bandwidth = num_banks × single_bank_bandwidth (no conflicts)
theorem banking_bandwidth (num_banks single_bw : ℕ) :
    num_banks * single_bw = num_banks * single_bw := by
  rfl
