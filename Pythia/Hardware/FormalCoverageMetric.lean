import Mathlib

-- Formal coverage analysis via mutation testing.
-- Measure how thorough a verification is by counting
-- how many spec mutations are killed by the proof.

variable {n : ℕ}

noncomputable def mutationKillRate (total killed : ℕ) : ℝ := killed / total

theorem kill_rate_le_one (total killed : ℕ) (h : killed ≤ total) (_ht : 0 < total) :
    mutationKillRate total killed ≤ 1 := by
  exact div_le_one_of_le₀ ( mod_cast h ) ( Nat.cast_nonneg _ )

theorem perfect_coverage (total : ℕ) (ht : 0 < total) :
    mutationKillRate total total = 1 := by
  exact div_self <| Nat.cast_ne_zero.mpr ht.ne'

theorem more_kills_better_coverage (total k1 k2 : ℕ) (h : k1 ≤ k2) (_ht : 0 < total) :
    mutationKillRate total k1 ≤ mutationKillRate total k2 := by
  exact div_le_div_of_nonneg_right ( Nat.cast_le.mpr h ) ( Nat.cast_nonneg _ )
