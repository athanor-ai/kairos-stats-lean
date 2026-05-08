/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sliding Window Attention

Sliding window attention (Beltagy et al. 2020, Longformer; Child et al. 2019,
Sparse Transformer) is a memory-efficient variant of causal attention in which
each position `i` only attends to the `W` most recent positions:

  windowSet i W = { j : Fin n | j ≤ i  ∧  i - j < W }   (causal, last-W window)

The softmax is restricted to this set. Outside the window the weight is 0.

## Key properties

1. Every window-attended position is also causally attended — the window mask
   is stricter than causal masking (subset).
2. Softmax outputs are non-negative.
3. Window weights sum to ≤ 1 (equal to 1 when the window is non-empty).
4. Positions outside the window receive exactly weight 0.
5. Monotonicity: enlarging the window includes all previously included positions.
6. When W ≥ n (full context), sliding window coincides with causal attention.

## Main results

* `sliding_window_is_partial_causal` — window set ⊆ causal set
* `sliding_window_nonneg`           — weights are non-negative
* `sliding_window_sum_le_one`       — weights sum to ≤ 1
* `sliding_window_zero_outside`     — weight is 0 outside the window
* `window_size_monotone`            — monotonicity of window sets
* `full_window_eq_causal`           — W ≥ n implies window = causal

## References

* Beltagy, I., Peters, M. E., Cohan, A. "Longformer: The Long-Document
  Transformer." arXiv:2004.05150 (2020).
* Child, R., Gray, S., Radford, A., Sutskever, I. "Generating Long Sequences
  with Sparse Transformers." arXiv:1904.10509 (2019).
-/
import Mathlib

namespace Pythia.Numerical.SlidingWindowAttention

open Finset BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Window set definitions -/

/-- The causal set for position `i`: all positions j ≤ i. -/
def causalSet (i : Fin n) : Finset (Fin n) :=
  Finset.filter (fun j => j ≤ i) Finset.univ

/-- The sliding window set for position `i` with window size `W`:
    positions j with j ≤ i and i - j < W (i.e., the last W causal positions). -/
def windowSet (W : ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.filter (fun j => j ≤ i ∧ i.val - j.val < W) Finset.univ

/-! ## Softmax restricted to a finset -/

/-- Sum of exponentials over a finset S of logits. -/
def expSum (logits : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, Real.exp (logits j)

/-- Sliding window attention weight: softmax restricted to windowSet W i. -/
def slidingWeight (logits : Fin n → ℝ) (W : ℕ) (i j : Fin n) : ℝ :=
  if j ∈ windowSet W i then
    Real.exp (logits j) / expSum logits (windowSet W i)
  else 0

/-- Causal attention weight: softmax restricted to causalSet i. -/
def causalWeight (logits : Fin n → ℝ) (i j : Fin n) : ℝ :=
  if j ∈ causalSet i then
    Real.exp (logits j) / expSum logits (causalSet i)
  else 0

/-! ## Lemmas about the sets -/

theorem causalSet_nonempty (i : Fin n) : (causalSet i).Nonempty :=
  ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩⟩

theorem causalSet_sum_pos (logits : Fin n → ℝ) (i : Fin n) :
    0 < expSum logits (causalSet i) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) (causalSet_nonempty i)

theorem mem_causalSet_iff (i j : Fin n) : j ∈ causalSet i ↔ j ≤ i := by
  simp [causalSet]

theorem mem_windowSet_iff (W : ℕ) (i j : Fin n) :
    j ∈ windowSet W i ↔ j ≤ i ∧ i.val - j.val < W := by
  simp [windowSet]

/-! ## Main theorems -/

/-- **Theorem 1: Sliding window attention is a subset of causal attention.**

Every position in the window set is also in the causal set. The window
mask is strictly more restrictive (unless W ≥ n, see `full_window_eq_causal`). -/
theorem sliding_window_is_partial_causal (W : ℕ) (i : Fin n) :
    windowSet W i ⊆ causalSet i := by
  intro j hj
  rw [mem_windowSet_iff] at hj
  rw [mem_causalSet_iff]
  exact hj.1

/-- **Theorem 2: Sliding window attention weights are non-negative.**

Each weight is either 0 (outside window) or exp(·)/Σexp(·) ≥ 0 (inside). -/
theorem sliding_window_nonneg (logits : Fin n → ℝ) (W : ℕ) (i j : Fin n) :
    0 ≤ slidingWeight logits W i j := by
  unfold slidingWeight
  split_ifs with h
  · apply div_nonneg
    · exact le_of_lt (Real.exp_pos _)
    · exact Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
  · exact le_refl 0

/-- **Theorem 3: Sliding window attention weights sum to ≤ 1.**

The sum over ALL positions j is ≤ 1: it equals 1 when the window is
non-empty, and 0 (hence ≤ 1) when the window is empty. -/
theorem sliding_window_sum_le_one (logits : Fin n → ℝ) (W : ℕ) (i : Fin n) :
    ∑ j : Fin n, slidingWeight logits W i j ≤ 1 := by
  by_cases hne : (windowSet W i).Nonempty
  · -- window is nonempty: the sum equals 1
    have hS_pos : 0 < expSum logits (windowSet W i) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) hne
    -- outside the window every term is 0, so univ-sum = window-sum
    have key : ∑ j : Fin n, slidingWeight logits W i j =
        ∑ j ∈ windowSet W i, slidingWeight logits W i j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj_notin
      exact if_neg hj_notin
    -- over the window the sum is exactly 1
    have window_one : ∑ j ∈ windowSet W i, slidingWeight logits W i j = 1 := by
      have step : ∀ j ∈ windowSet W i, slidingWeight logits W i j =
          Real.exp (logits j) / expSum logits (windowSet W i) :=
        fun j hj => if_pos hj
      rw [Finset.sum_congr rfl step, ← Finset.sum_div]
      exact div_self (ne_of_gt hS_pos)
    linarith [key ▸ window_one]
  · -- window is empty: all weights are 0
    have hempty : windowSet W i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have : ∑ j : Fin n, slidingWeight logits W i j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [slidingWeight, hempty]
    linarith

/-- **Theorem 4: Positions outside the sliding window get zero weight.**

If `j` is not in the window set of `i`, then `slidingWeight logits W i j = 0`. -/
theorem sliding_window_zero_outside (logits : Fin n → ℝ) (W : ℕ) (i j : Fin n)
    (hj : j ∉ windowSet W i) :
    slidingWeight logits W i j = 0 :=
  if_neg hj

/-- **Theorem 5: Window size monotonicity.**

If W ≤ W', then every position included by window W is also included
by window W'. Larger windows are supersets of smaller windows. -/
theorem window_size_monotone (W W' : ℕ) (hWW' : W ≤ W') (i : Fin n) :
    windowSet W i ⊆ windowSet W' i := by
  intro j hj
  rw [mem_windowSet_iff] at hj ⊢
  exact ⟨hj.1, Nat.lt_of_lt_of_le hj.2 hWW'⟩

/-- **Theorem 6: Full window equals causal attention.**

When the window size W ≥ n (the sequence length), every causally
reachable position fits in the window, so the window set equals the
causal set and the two attention mechanisms coincide exactly. -/
theorem full_window_eq_causal (logits : Fin n → ℝ) (W : ℕ) (hW : n ≤ W)
    (i j : Fin n) :
    slidingWeight logits W i j = causalWeight logits i j := by
  have hsets : windowSet W i = causalSet i := by
    ext k
    rw [mem_windowSet_iff, mem_causalSet_iff]
    constructor
    · intro ⟨hki, _⟩; exact hki
    · intro hki
      refine ⟨hki, ?_⟩
      -- i.val - k.val ≤ i.val < n ≤ W
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le i.isLt hW)
  simp only [slidingWeight, causalWeight, hsets]

/-! ## Auxiliary: window sum equals 1 when window is nonempty -/

/-- When the window is nonempty, the weights over the window itself sum to 1. -/
theorem sliding_window_sum_window_eq_one (logits : Fin n → ℝ) (W : ℕ) (i : Fin n)
    (hne : (windowSet W i).Nonempty) :
    ∑ j ∈ windowSet W i, slidingWeight logits W i j = 1 := by
  have hS_pos : 0 < expSum logits (windowSet W i) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hne
  have step : ∀ j ∈ windowSet W i, slidingWeight logits W i j =
      Real.exp (logits j) / expSum logits (windowSet W i) :=
    fun j hj => if_pos hj
  rw [Finset.sum_congr rfl step, ← Finset.sum_div]
  exact div_self (ne_of_gt hS_pos)

/-- Position `i` always belongs to its own window when W ≥ 1. -/
theorem windowSet_self_mem (W : ℕ) (hW : 0 < W) (i : Fin n) :
    i ∈ windowSet W i := by
  rw [mem_windowSet_iff]
  exact ⟨le_refl _, by simp [hW]⟩

end

end Pythia.Numerical.SlidingWindowAttention
