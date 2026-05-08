/-
Pythia.Hardware.OneHotMux — one-hot multiplexer correctness.

Core invariant for hardware mux verification: a selector bus is
one-hot when exactly one bit is asserted.  Every synthesised mux in
a data-path or priority encoder chains through this; machine-checking
it at the Lean level means the RTL property holds at proof strength.

Theorems proved:
  one_hot_unique            — the selected index is uniquely determined
  one_hot_mux_selects       — mux output equals the input at that index
  one_hot_preserved_by_decoder — binary-to-one-hot decoder is one-hot
  one_hot_at_most_one       — one-hot implies at most one true bit

Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0; see LICENSE for details.
-/

import Mathlib

namespace Pythia.Hardware.OneHotMux

/-! ## One-hot predicate -/

/-- A selector vector is *one-hot* when exactly one component is `true`. -/
def isOneHot {n : ℕ} (sel : Fin n → Bool) : Prop :=
  ∃! i, sel i = true

/-! ## Multiplexer model -/

/-- `muxOutput inputs sel default` returns `inputs i` when `sel` is
one-hot at `i`, and `default` otherwise.  Using `Finset.filter` keeps
the model close to RTL; the definition is noncomputable because
`Multiset.toList` requires a choice of ordering on the universe. -/
noncomputable def muxOutput {n : ℕ} {α : Type*} [Zero α]
    (inputs : Fin n → α) (sel : Fin n → Bool) (default : α) : α :=
  match (Finset.univ.filter (fun i => sel i)).val.toList with
  | [i] => inputs i
  | _   => default

/-! ## Theorem 1 — uniqueness of the selected index -/

/-- If `sel` is one-hot then any two witnesses for `sel · = true` are
equal: the selected index is unique. -/
theorem one_hot_unique {n : ℕ} (sel : Fin n → Bool)
    (h : isOneHot sel) (i j : Fin n)
    (hi : sel i = true) (hj : sel j = true) : i = j := by
  obtain ⟨k, _hk, huniq⟩ := h
  have hik : i = k := huniq i hi
  have hjk : j = k := huniq j hj
  omega

/-! ## Theorem 4 — at most one true bit -/

/-- One-hot implies at most one `true` bit: the filter set has
cardinality ≤ 1. -/
theorem one_hot_at_most_one {n : ℕ} (sel : Fin n → Bool)
    (h : isOneHot sel) :
    (Finset.univ.filter (fun i : Fin n => sel i)).card ≤ 1 := by
  obtain ⟨k, hk, huniq⟩ := h
  have hsub : Finset.univ.filter (fun i : Fin n => sel i) ⊆ {k} := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_singleton]
    exact huniq x hx
  calc (Finset.univ.filter (fun i : Fin n => sel i)).card
      ≤ ({k} : Finset (Fin n)).card := Finset.card_le_card hsub
    _ = 1                           := Finset.card_singleton k

/-! ## Helper: the filter Finset equals a singleton -/

private theorem one_hot_filter_eq_singleton {n : ℕ} (sel : Fin n → Bool)
    (h : isOneHot sel) :
    ∃ k : Fin n, Finset.univ.filter (fun i : Fin n => sel i) = {k} ∧ sel k = true := by
  obtain ⟨k, hk, huniq⟩ := h
  refine ⟨k, ?_, hk⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨huniq x, fun hxk => hxk ▸ hk⟩

/-! ## Theorem 2 — mux selects the right input -/

/-- When `sel` is one-hot at index `i`, `muxOutput` returns `inputs i`
regardless of the default value. -/
theorem one_hot_mux_selects {n : ℕ} {α : Type*} [Zero α]
    (inputs : Fin n → α) (sel : Fin n → Bool) (default : α) (i : Fin n)
    (h : isOneHot sel) (hi : sel i = true) :
    muxOutput inputs sel default = inputs i := by
  obtain ⟨k, hkeq, hk⟩ := one_hot_filter_eq_singleton sel h
  -- k and i are equal: both satisfy sel · = true under a one-hot selector
  have hki : k = i := one_hot_unique sel h k i hk hi
  -- Reduce the toList of a singleton Finset to a singleton list
  have hlist : (Finset.univ.filter (fun j : Fin n => sel j)).val.toList = [k] := by
    rw [hkeq, Finset.singleton_val, Multiset.toList_singleton]
  simp only [muxOutput, hlist, hki]

/-! ## Binary-to-one-hot decoder -/

/-- The canonical binary-to-one-hot decoder: given `i : Fin n`, produce
the selector that is `true` exactly at position `i`. -/
def binaryToOneHot {n : ℕ} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

/-! ## Theorem 3 — decoder produces one-hot output -/

/-- `binaryToOneHot i` is always one-hot: the unique `true` position is `i`. -/
theorem one_hot_preserved_by_decoder {n : ℕ} (i : Fin n) :
    isOneHot (binaryToOneHot i) := by
  unfold isOneHot binaryToOneHot
  refine ⟨i, by simp, fun j hj => ?_⟩
  simp only [decide_eq_true_eq] at hj
  exact hj

end Pythia.Hardware.OneHotMux
