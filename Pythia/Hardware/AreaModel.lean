import Mathlib

-- Area model for optimization gate: formal relationship
-- between gate count and chip area. Phase 2 infrastructure.

def cellArea (gate_count : ℕ) (avg_cell_area : ℝ) : ℝ :=
  gate_count * avg_cell_area

/-
Fewer gates means less area
-/
theorem fewer_gates_less_area (g1 g2 : ℕ) (avg : ℝ) (h_avg : 0 < avg) (h : g1 < g2) :
    cellArea g1 avg < cellArea g2 avg := by
  exact mul_lt_mul_of_pos_right ( Nat.cast_lt.mpr h ) h_avg

-- Area reduction percentage
noncomputable def areaReduction (original optimized : ℕ) (avg : ℝ) : ℝ :=
  (cellArea original avg - cellArea optimized avg) / cellArea original avg

/-
Positive reduction when optimized < original
-/
theorem positive_reduction (orig opt : ℕ) (avg : ℝ)
    (h_avg : 0 < avg) (h_opt : opt < orig) (h_orig : 0 < orig) :
    0 < areaReduction orig opt avg := by
  exact div_pos ( sub_pos_of_lt ( mul_lt_mul_of_pos_right ( mod_cast h_opt ) h_avg ) ) ( mul_pos ( mod_cast h_orig ) h_avg )