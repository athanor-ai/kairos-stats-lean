import Mathlib

open Finset

-- Compositional propagation: one-hot property propagates through mux select.
-- If arbiter grant is one-hot and drives mux select, then mux select is one-hot.
-- More generally: one-hot is preserved by identity wiring and permutation.

variable {n : ℕ}

def isOneHot (f : Fin n → Bool) : Prop := ∃! i, f i = true

-- One-hot propagated through identity (direct wiring)
theorem one_hot_propagate_id (f : Fin n → Bool) (h : isOneHot f) :
    isOneHot f := h

/-
One-hot propagated through permutation (reordering wires)
-/
theorem one_hot_propagate_perm (f : Fin n → Bool) (σ : Equiv.Perm (Fin n))
    (h : isOneHot f) : isOneHot (f ∘ σ) := by
  obtain ⟨ i, hi, hiu ⟩ := h;
  exact ⟨ σ.symm i, by aesop, fun y hy => σ.injective <| by aesop ⟩

/-
One-hot propagated through subsetting (taking a subset of wires that includes the hot one)
-/
theorem one_hot_implies_at_most_one (f : Fin n → Bool) (h : isOneHot f)
    (i j : Fin n) (hi : f i = true) (hj : f j = true) : i = j := by
  cases h ; aesop

/-
One-hot grant drives mux: mux output is well-defined
-/
theorem one_hot_mux_well_defined {α : Type*} (inputs : Fin n → α) (sel : Fin n → Bool)
    (h : isOneHot sel) :
    ∃! i, sel i = true ∧ ∀ j, sel j = true → inputs j = inputs i := by
  obtain ⟨ i, hi, hiu ⟩ := h;
  exact ⟨ i, ⟨ hi, fun j hj => by rw [ hiu j hj ] ⟩, fun j hj => hiu j hj.1 ⟩

/-
Compositional: one-hot at stage k → one-hot at stage k+1 through a pipeline register
-/
theorem one_hot_through_register (f_curr f_next : Fin n → Bool)
    (h_curr : isOneHot f_curr)
    (h_reg : f_next = f_curr) : isOneHot f_next := by
  exact h_reg ▸ h_curr

/-
Bounded property propagation: if value at stage k is in [0, N),
then after applying a monotone bounded function, still in [0, M)
-/
theorem bounded_propagate {N M : ℕ} (x : ℕ) (hx : x < N)
    (f : ℕ → ℕ) (hf : ∀ y, y < N → f y < M) : f x < M := by
  exact hf x hx