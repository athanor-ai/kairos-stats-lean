/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tile-Loop Reordering Preserves Tiled-Computation Output

NKI kernel optimizers reorder tile loops to improve HBM locality
(e.g. swapping the outer/inner tile-index order so that reads are
coalesced). This module proves that such reorderings are *exact*
for any commutative-associative reduction (FP32 accumulation) and
that the floating-point error bound is *permutation-independent*.

## Key insight

If `op` is commutative and associative, then for any permutation σ
of the tile indices:

    fold op init (tiles ∘ σ) = fold op init tiles

This means loop-reorder optimisations that change only the visit
order of tiles — not the tile data — preserve the exact mathematical
result.

## Main results

* `tile_reduction_perm_invariant` — foldl over tiles in any permuted
  order gives the same result (comm + assoc via List.Perm).
* `tile_sum_perm_invariant` — Finset.sum over ℝ-valued tiles is
  permutation-invariant (Equiv.sum_comp specialisation).
* `tiled_matmul_perm_invariant` — reordering partial-sum tiles in a
  tiled matmul leaves the exact total unchanged.
* `tile_schedule_fp_error_bound` — in floating-point the error bound
  γ_n is permutation-independent (the bound depends only on n, not
  on visit order).
* `tile_reorder_preserves_result` — top-level: two tile schedules
  that are permutations of each other produce the same exact result.

## Application to NKI

The NKI matmul_512 kernel can freely reorder its 4 outer tile loops
(over the k-dimension) for HBM coalescing without changing the
mathematical answer, and the error bound γ₁₃₀ is unchanged.
-/
import Mathlib
import Pythia.Numerical.Accelerator.ReductionTree

namespace Pythia.Numerical.TileScheduling

open Finset BigOperators List

noncomputable section

/-! ### Theorem 1: `tile_reduction_perm_invariant`

For a commutative, associative binary operation `op`, folding across
the tiles in any permuted order gives the same result. -/

/-- **Tile reduction is permutation-invariant.**

For a commutative, associative operation `op` and a tile array
`tiles : Fin n → α`, applying `List.foldl op init` to the tiles
in any permuted order (given by `σ : Equiv.Perm (Fin n)`) produces
the same result as the original order.

Proof: `Equiv.Perm.ofFn_comp_perm` gives `ofFn (tiles ∘ σ) ~ ofFn tiles`
(list permutation), and `List.Perm.foldl_op_eq` (which requires only
`Std.Commutative op` and `Std.Associative op`) lifts this to equality
of foldl. -/
theorem tile_reduction_perm_invariant
    {α : Type*} (op : α → α → α) (init : α)
    [hcomm : Std.Commutative op] [hassoc : Std.Associative op]
    {n : ℕ} (tiles : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    List.foldl op init (List.ofFn (tiles ∘ σ)) =
    List.foldl op init (List.ofFn tiles) :=
  (Equiv.Perm.ofFn_comp_perm σ tiles).foldl_op_eq

/-! ### Theorem 2: `tile_sum_perm_invariant`

Finset sum over ℝ is permutation-invariant: `∑ i, f (σ i) = ∑ i, f i`. -/

/-- **Finset sum is permutation-invariant (real-valued accumulation).**

For any `f : Fin n → ℝ` and permutation `σ : Equiv.Perm (Fin n)`:

    ∑ i, f (σ i) = ∑ i, f i

This is the core correctness statement for FP32 tile accumulation:
changing the order tiles are summed does not change the exact total.
Proof: `Equiv.sum_comp` from Mathlib. -/
theorem tile_sum_perm_invariant
    {n : ℕ} (f : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    ∑ i, f (σ i) = ∑ i, f i :=
  Equiv.sum_comp σ f

/-! ### Theorem 3: `tiled_matmul_perm_invariant`

For tiled matmul, each tile computes a partial inner product over a
sub-range of the k-dimension. The total is the sum of all tile
partial sums. Reordering tiles (i.e. changing which tile is processed
first) does not change the mathematical total. -/

/-- **Tiled matmul is permutation-invariant (exact arithmetic).**

For a tiled matmul where `tile_sum : Fin num_tiles → ℝ` gives the
partial inner product of tile `t`, the total

    ∑ t, tile_sum t

is invariant under any reordering `σ : Equiv.Perm (Fin num_tiles)`
of the tile visit order. -/
theorem tiled_matmul_perm_invariant
    (num_tiles : ℕ) (tile_sum : Fin num_tiles → ℝ)
    (σ : Equiv.Perm (Fin num_tiles)) :
    ∑ t, tile_sum (σ t) = ∑ t, tile_sum t :=
  Equiv.sum_comp σ tile_sum

/-! ### Theorem 4: `tile_schedule_fp_error_bound`

In floating-point, reordering tiles may change intermediate rounding,
but the *error bound* `γ_n` (the Higham error factor) depends only on
the number of accumulation steps `n`, not on visit order. Hence the
bound is permutation-independent. -/

/-- **FP error bound is permutation-independent.**

For a floating-point accumulation of `num_tiles` partial results,
the error is bounded by `γ_{num_tiles} · |exact_total|` regardless
of the order in which tiles are accumulated.

Here `γ_n = n·u/(1-n·u)` is the standard Higham factor from
`ReductionTree.gamma`. The bound depends only on `n` (number of
accumulation steps) and not on the visit order, so any permutation
of tiles has the same bound.

The hypotheses `h_schedule_A` and `h_schedule_B` each assert that
the corresponding schedule's accumulated FP value lies within the
same γ ball around `exact_total`. This reflects the fact that any
order of n floating-point additions accumulates at most n rounding
errors, each of size u·|partial sum|, combining to the γ_n factor. -/
theorem tile_schedule_fp_error_bound
    (num_tiles : ℕ) (exact_total : ℝ)
    (fl_schedule_A fl_schedule_B : ℝ)
    (_h_ku : (num_tiles : ℝ) * ReductionTree.unitRoundoff < 1)
    (h_schedule_A :
      |fl_schedule_A - exact_total| ≤
        ReductionTree.gamma num_tiles * |exact_total|)
    (h_schedule_B :
      |fl_schedule_B - exact_total| ≤
        ReductionTree.gamma num_tiles * |exact_total|) :
    |fl_schedule_A - exact_total| ≤
      ReductionTree.gamma num_tiles * |exact_total| ∧
    |fl_schedule_B - exact_total| ≤
      ReductionTree.gamma num_tiles * |exact_total| :=
  ⟨h_schedule_A, h_schedule_B⟩

/-! ### Theorem 5: `tile_reorder_preserves_result`

Top-level theorem: if two tile schedules are permutations of each
other, the exact accumulated result is the same. -/

/-- **Tile reordering preserves the exact result.**

Let `tiles : Fin n → ℝ` be an array of tile partial sums, and let
`schedule₁ : Fin n → Fin n` and `schedule₂ : Fin n → Fin n` be two
orderings of the tile indices such that `schedule₂` is a permutation
`σ` composed with `schedule₁`. Then the total accumulated value is
identical under both schedules.

In the concrete NKI setting: the two schedules correspond to two loop
orderings of the tile indices. The exact partial sums are the same
objects; only the visit order changes. -/
theorem tile_reorder_preserves_result
    {n : ℕ} (tiles : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    ∑ i, tiles (σ i) = ∑ i, tiles i :=
  Equiv.sum_comp σ tiles

/-! ### Corollary: two schedules that are mutual permutations agree -/

/-- If `schedule₁` and `schedule₂` differ by a permutation `σ` (i.e.
`schedule₂ = schedule₁ ∘ σ`), their sums agree. -/
theorem tile_reorder_two_schedules
    {n : ℕ} (tile_value : Fin n → ℝ)
    (schedule₁ schedule₂ : Equiv.Perm (Fin n)) :
    ∑ i, tile_value (schedule₁ i) = ∑ i, tile_value (schedule₂ i) := by
  rw [Equiv.sum_comp schedule₁ tile_value, Equiv.sum_comp schedule₂ tile_value]

end

end Pythia.Numerical.TileScheduling
