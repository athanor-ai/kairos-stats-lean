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
Fewer gates means fewer or equal total toggles (tight bound).
The optimized circuit's gates (`gates'`) are a restriction of the original
circuit's gates via the injection `Fin.castLE hk : Fin k → Fin m`.
Since `Fin.castLE hk` is injective, the image of `Finset.univ (Fin k)` under
it is a sub-multiset of `Finset.univ (Fin m)`, so the sum over k gates is at
most the sum over all m gates.  No 2× slack is needed.
-/
theorem fewer_gates_fewer_toggles
    (k : ℕ) (hk : k ≤ m)
    (gates : Fin m → ((Fin n → Bool) → Bool))
    (gates' : Fin k → ((Fin n → Bool) → Bool))
    (h_restrict : ∀ i : Fin k, gates' i = gates (Fin.castLE hk i))
    (inputs : List (Fin n → Bool)) :
    ∑ i : Fin k, toggleCount (gates' i) inputs ≤
    ∑ i : Fin m, toggleCount (gates i) inputs := by
  -- Rewrite LHS: replace gates' i with gates (Fin.castLE hk i) everywhere.
  conv_lhs =>
    arg 2; ext i; rw [h_restrict i]
  -- After rewriting, the LHS is ∑ i : Fin k, toggleCount (gates (Fin.castLE hk i)) inputs.
  -- Reindex as a sum over the image of Fin.castLE hk inside Finset.univ (Fin m).
  have h_inj : Function.Injective (Fin.castLE hk) := Fin.castLE_injective hk
  rw [← Finset.sum_image (f := fun j => toggleCount (gates j) inputs)
        (by intros a _ b _ hab; exact h_inj hab)]
  -- The image is a subset of Finset.univ, so its sum is ≤ the full sum.
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)