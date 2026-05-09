import Mathlib

open Finset BigOperators

-- Toggle power preservation: removing redundant gates reduces toggle activity.
-- If an optimization removes a gate while preserving the circuit function,
-- the removed gate's toggles are eliminated.

variable {n m : ℕ}

-- A circuit is a function from inputs to gate values
-- Toggle count: number of input transitions that cause a gate to change output
def toggleCount (gate : (Fin n → Bool) → Bool) (inputs : List (Fin n → Bool)) : ℕ :=
  (inputs.zip inputs.tail).countP fun ⟨a, b⟩ => gate a != gate b

/-
If a gate is redundant (output equals another gate), removing it
doesn't change the circuit function but eliminates its toggles
-/
theorem redundant_gate_zero_additional_toggles
    (gate1 gate2 : (Fin n → Bool) → Bool)
    (h_equiv : ∀ input, gate1 input = gate2 input)
    (inputs : List (Fin n → Bool)) :
    toggleCount gate1 inputs = toggleCount gate2 inputs := by
  unfold toggleCount; congr! 2; aesop;

/-
Total toggle count is sum of per-gate toggles
Removing a gate reduces total toggles
-/
theorem remove_gate_reduces_toggles
    (gates : Fin (m + 1) → ((Fin n → Bool) → Bool))
    (removed : Fin (m + 1))
    (inputs : List (Fin n → Bool)) :
    ∑ i ∈ Finset.univ.erase removed, toggleCount (gates i) inputs ≤
    ∑ i, toggleCount (gates i) inputs := by
  exact Finset.sum_le_sum_of_subset ( Finset.erase_subset _ _ )

/-
Fewer gates means fewer or equal total toggles (upper bound).
The optimized circuit's gates (`gates'`) must be a restriction of the original
circuit's first `k` gates. The original statement with arbitrary `gates'` was
false (counterexample: `gates` constant, `gates'` toggling). Added hypothesis
`h_restrict` to relate `gates'` to `gates`. The `2×` slack on the RHS follows
from `Finset.sum_nonneg`.
-/
theorem fewer_gates_fewer_toggles
    (k : ℕ) (hk : k ≤ m)
    (gates : Fin m → ((Fin n → Bool) → Bool))
    (gates' : Fin k → ((Fin n → Bool) → Bool))
    (h_restrict : ∀ i : Fin k, gates' i = gates (Fin.castLE hk i))
    (inputs : List (Fin n → Bool)) :
    ∑ i : Fin k, toggleCount (gates' i) inputs ≤
    ∑ i : Fin m, toggleCount (gates i) inputs +
      ∑ i : Fin m, toggleCount (gates i) inputs := by
  -- By definition of `gates'`, we can replace each `gates' i` with `gates (Fin.castLE hk i)` in the sum.
  have h_sum_restrict : ∑ i, toggleCount (gates' i) inputs = ∑ i ∈ Finset.univ.image (Fin.castLE hk), toggleCount (gates i) inputs := by
    rw [ Finset.sum_image <| by intros a ha b hb hab; simpa [ Fin.ext_iff ] using hab ] ; aesop;
  exact h_sum_restrict.symm ▸ le_add_of_le_of_nonneg ( Finset.sum_le_sum_of_subset ( Finset.subset_univ _ ) ) ( Nat.zero_le _ )