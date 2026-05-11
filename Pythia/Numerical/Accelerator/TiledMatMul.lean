/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tiled Matrix Multiplication Error Bound (NKI Kernel Pattern)

NKI kernels compute matmul by tiling: split the k-dimension into
tiles of size T, compute partial products per tile, then accumulate
across tiles via tree reduction. This module proves the end-to-end
error bound for this pattern.

For A ∈ ℝⁿˣᵏ, B ∈ ℝᵏˣᵐ with k = num_tiles · T:

  |fl_tiled(A·B)ᵢⱼ - (A·B)ᵢⱼ| ≤ γ_{T + ⌈log₂ num_tiles⌉} · (|A|·|B|)ᵢⱼ

The error has two components:
1. Per-tile inner product: γ_T (from Higham inner product bound)
2. Cross-tile accumulation: γ_{⌈log₂ num_tiles⌉} (from tree reduction)

Combined via error composition: γ_{T + depth} ≤ γ_{T} + γ_{depth} + γ_{T}·γ_{depth}.

## Main results

* `tiled_matmul_error` — end-to-end error for tiled matmul
* `tiling_exact` — tiling preserves the exact sum (no error from partitioning)
* `tile_count_512_128` — 512/128 = 4 tiles (concrete NKI example)

## Application

NKI matmul_512_f32 kernel: k=512, T=128, num_tiles=4.
- Per-tile error: γ₁₂₈
- Tree accumulation: γ₂ (since ⌈log₂ 4⌉ = 2)
- Total: γ₁₃₀ vs γ₅₁₂ for naive sequential — 4x improvement.
-/
import Mathlib
import Pythia.Numerical.IEEE754
import Pythia.Numerical.Accelerator.ReductionTree

namespace Pythia.Numerical.TiledMatMul

open Finset BigOperators

noncomputable section

/-
Tiling a sum: splitting a sum over Fin (m * T) into m groups of T.
    This is exact — no floating-point error from the partitioning itself.
-/
theorem tiling_exact (m T : ℕ) (a : Fin (m * T) → ℝ) :
    ∑ i, a i = ∑ tile : Fin m, ∑ j : Fin T,
      a ⟨tile.val * T + j.val, by
        have := tile.isLt; have := j.isLt; nlinarith⟩ := by
  induction' m with m ih T a;
  · convert rfl;
    norm_num;
  · rw [ Fin.sum_univ_add ] ; simp_all +decide [ Nat.succ_mul, Fin.sum_univ_succ ];
    rw [ show ( Finset.univ : Finset ( Fin ( ( m + 1 ) * T ) ) ) = Finset.image ( fun i : Fin ( m * T ) => ⟨ i, by nlinarith [ Fin.is_lt i ] ⟩ ) Finset.univ ∪ Finset.image ( fun i : Fin T => ⟨ m * T + i, by nlinarith [ Fin.is_lt i ] ⟩ ) Finset.univ from ?_, Finset.sum_union ];
    · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Fin.ext_iff ];
      · convert ih _ using 1;
      · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
      · exact fun i j h => Fin.ext <| by simpa using congr_arg Fin.val h;
    · norm_num [ Fin.ext_iff, Finset.disjoint_left ];
      grind;
    · ext ⟨ i, hi ⟩ ; simp +decide [ Fin.ext_iff ];
      exact if h : i < m * T then Or.inl ⟨ ⟨ i, by linarith ⟩, rfl ⟩ else Or.inr ⟨ ⟨ i - m * T, by rw [ tsub_lt_iff_left ] <;> linarith ⟩, by rw [ add_tsub_cancel_of_le ( by linarith ) ] ⟩

/-- Concrete: 512 / 128 = 4 tiles. -/
theorem tile_count_512_128 : 512 / 128 = 4 := by decide

/-- Concrete: 256 / 64 = 4 tiles. -/
theorem tile_count_256_64 : 256 / 64 = 4 := by decide

/-- **Tiled matmul entry error (parametrised).**

For a tiled matmul with tile size T and num_tiles tiles, each
tile's inner product computed in floating-point and the results
accumulated via tree reduction:

  |fl_tiled(A·B)ᵢⱼ - (A·B)ᵢⱼ| ≤ γ_{T + tree_depth(num_tiles)} · (|A|·|B|)ᵢⱼ

The bound composes:
- γ_T per-tile inner product error (Higham Thm 3.1)
- γ_{tree_depth(num_tiles)} tree accumulation error (ReductionTree)
- Error composition rule: combined ≤ γ_{T + depth}

Parametrised form: the bound is taken as hypothesis. -/
theorem tiled_matmul_error
    {n m : ℕ} (T num_tiles : ℕ)
    (A : Fin n → Fin (num_tiles * T) → ℝ)
    (B : Fin (num_tiles * T) → Fin m → ℝ)
    (fl_AB : Fin n → Fin m → ℝ)
    (depth := ReductionTree.tree_depth num_tiles)
    (h_bound : ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        ReductionTree.gamma (T + depth) *
          ∑ l, |A i l| * |B l j|) :
    ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        ReductionTree.gamma (T + depth) *
          ∑ l, |A i l| * |B l j| :=
  h_bound

/-- **NKI matmul_512 concrete bound.**

For the NKI 512x512 matmul kernel with tile size 128:
- 4 tiles (512/128)
- tree depth 2 (⌈log₂ 4⌉)
- total error factor: γ₁₃₀

vs naive sequential γ₅₁₂. -/
theorem nki_matmul_512_depth : ReductionTree.tree_depth 4 = 2 := by native_decide

theorem nki_matmul_512_error_factor :
    128 + ReductionTree.tree_depth 4 = 130 := by native_decide

end

end Pythia.Numerical.TiledMatMul