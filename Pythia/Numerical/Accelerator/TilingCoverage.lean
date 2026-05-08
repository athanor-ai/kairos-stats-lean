/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rectangular Tiling Coverage

A rectangular M×N matrix is tiled into blocks of size T_M × T_N where
T_M | M and T_N | N. This module proves the tiling is a valid partition:

1. **Covers** — every (i,j) belongs to some tile.
2. **Unique** — the tile assignment is deterministic (at most one tile per element).
3. **Tile count** — total number of tiles is (M/T_M) * (N/T_N).
4. **Tile size** — each tile contains exactly T_M * T_N elements.

## Definitions

* `tileIndex i j T_M T_N` — which tile contains element (i,j)
* `tileElements M N T_M T_N ti tj` — finset of elements in tile (ti,tj)

## Main results

* `tiling_covers` — every element belongs to some tile
* `tiling_unique` — tile assignment is deterministic; each element in at most one tile
* `tile_count` — number of distinct tiles = (M / T_M) * (N / T_N)
* `tile_size` — each tile has exactly T_M * T_N elements (when T_M | M and T_N | N)
-/
import Mathlib

namespace Pythia.Numerical.TilingCoverage

open Finset

/-! ### Definitions -/

/-- Which tile contains element (i, j): the index pair (i/T_M, j/T_N). -/
def tileIndex (M N : ℕ) (i : Fin M) (j : Fin N) (T_M T_N : ℕ) : ℕ × ℕ :=
  (i.val / T_M, j.val / T_N)

/-- The finset of all matrix elements belonging to tile (ti, tj). -/
def tileElements (M N T_M T_N ti tj : ℕ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun p => p.1.val / T_M = ti ∧ p.2.val / T_N = tj

/-! ### Theorem 1: every element is covered -/

/-- Every element (i, j) belongs to the tile `tileIndex i j T_M T_N`. -/
theorem tiling_covers (M N T_M T_N : ℕ) (i : Fin M) (j : Fin N) :
    (i, j) ∈ tileElements M N T_M T_N (i.val / T_M) (j.val / T_N) := by
  simp [tileElements]

/-! ### Theorem 2: tile assignment is unique (deterministic) -/

/-- If (i, j) is in tile (ti, tj) then ti = i/T_M and tj = j/T_N.
    Hence each element belongs to at most one tile. -/
theorem tiling_unique (M N T_M T_N : ℕ) (i : Fin M) (j : Fin N)
    (ti tj : ℕ) (h : (i, j) ∈ tileElements M N T_M T_N ti tj) :
    ti = i.val / T_M ∧ tj = j.val / T_N := by
  simp [tileElements] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-! ### Theorem 3: tile count -/

/-- The finset of all valid tile indices (ti, tj). -/
def tileIndices (M N T_M T_N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (M / T_M)) ×ˢ (Finset.range (N / T_N))

/-- Total number of distinct tiles is (M / T_M) * (N / T_N). -/
theorem tile_count (M N T_M T_N : ℕ) :
    (tileIndices M N T_M T_N).card = (M / T_M) * (N / T_N) := by
  simp [tileIndices, Finset.card_product]

/-! ### Theorem 4: tile size — auxiliary card lemma -/

/-- The number of indices in Fin M whose value, divided by T, equals ti,
    is exactly T (when T | M and ti is a valid tile index). -/
private lemma filter_div_card (M' T ti : ℕ) (hTpos : 0 < T) (hTdvd : T ∣ M')
    (hti : ti < M' / T) :
    (Finset.univ (α := Fin M') |>.filter (fun i => i.val / T = ti)).card = T := by
  -- Exhibit a bijection to Finset.range T, then use card_range
  suffices h : (Finset.univ (α := Fin M') |>.filter (fun i => i.val / T = ti)).card =
      (Finset.range T).card from by simp [Finset.card_range] at h; exact h
  apply Finset.card_bij (fun (i : Fin M') _ => i.val % T)
  · -- The residue lands in range T
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_range.mpr (Nat.mod_lt _ hTpos)
  · -- Injectivity: distinct elements in the same tile row have distinct residues
    intro ⟨a, ha⟩ hma ⟨b, hb⟩ hmb heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hma hmb
    simp only at heq
    -- Both equal T*ti + (their residue)
    have ha' : a = T * ti + a % T := by
      have := (Nat.div_add_mod a T).symm; rw [hma] at this; linarith
    have hb' : b = T * ti + b % T := by
      have := (Nat.div_add_mod b T).symm; rw [hmb] at this; linarith
    simp only [Fin.mk.injEq]; omega
  · -- Surjectivity: for each k < T there is T*ti+k in the tile row
    intro k hk
    rw [Finset.mem_range] at hk
    have hM : T * (M' / T) = M' := Nat.mul_div_cancel' hTdvd
    have hbound : T * ti + k < M' := by
      calc T * ti + k < T * ti + T := by omega
        _ = T * (ti + 1)          := by ring
        _ ≤ T * (M' / T)          := by nlinarith
        _ = M'                     := hM
    refine ⟨⟨T * ti + k, hbound⟩, ?_, ?_⟩
    · -- T * ti + k lives in tile row ti
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Nat.mul_add_div hTpos, Nat.div_eq_of_lt hk, add_zero]
    · -- Its residue mod T is k
      simp only
      rw [show T * ti + k = k + T * ti by ring]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

/-! ### Theorem 4: tile size -/

/-- Each tile has exactly T_M * T_N elements when T_M | M, T_N | N,
    and the tile index is in range. -/
theorem tile_size (M N T_M T_N ti tj : ℕ)
    (hTMpos : 0 < T_M) (hTNpos : 0 < T_N)
    (hTM : T_M ∣ M) (hTN : T_N ∣ N)
    (hti : ti < M / T_M) (htj : tj < N / T_N) :
    (tileElements M N T_M T_N ti tj).card = T_M * T_N := by
  rw [tileElements]
  -- Factor the filter over the product as a cartesian product of two row/col filters
  have heq :
      Finset.univ.filter (fun p : Fin M × Fin N => p.1.val / T_M = ti ∧ p.2.val / T_N = tj) =
      (Finset.univ.filter (fun i : Fin M => i.val / T_M = ti)) ×ˢ
      (Finset.univ.filter (fun j : Fin N => j.val / T_N = tj)) := by
    ext ⟨i, j⟩
    simp [Finset.mem_product, Finset.mem_filter]
  rw [heq, Finset.card_product,
      filter_div_card M T_M ti hTMpos hTM hti,
      filter_div_card N T_N tj hTNpos hTN htj]

end Pythia.Numerical.TilingCoverage
