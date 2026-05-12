/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Memory Tile Identity — SBUF Reuse Soundness (Accelerator Kernel Optimization)

Accelerator kernels can eliminate redundant HBM loads by caching tiles in the
scratchpad buffer (SBUF). This module proves that reusing a cached tile
is sound: if no write to HBM or SBUF has occurred since the original
load, the cached tile equals the HBM tile.

## State model

```
structure SBUFState (n : ℕ) (α : Type*) where
  sbuf : Fin n → α   -- scratchpad buffer (tile index → tile data)
  hbm  : Fin n → α   -- HBM (tile index → tile data)
```

Operations:
* `sbufLoad`  — copies HBM[i] into SBUF[i] (models an accelerator `nl.load`)
* `sbufReuse` — reads SBUF[i] without a load (models reuse)
* `hbmWrite`  — writes a new value to HBM[i] (models an HBM update)
* `sbufWrite` — writes a new value to SBUF[i] (models an explicit SBUF update)

## Main results

* `sbuf_load_stores_tile`     — after `sbufLoad i`, SBUF[i] = HBM[i]
* `sbuf_reuse_eq_load`        — if HBM[i] unchanged since load, SBUF[i] = HBM[i]
* `no_write_preserves_sbuf`   — if no write to SBUF[i], SBUF[i] is unchanged
* `redundant_load_elimination` — loading the same tile twice (no HBM change) is idempotent
* `sbuf_isolation`             — loading tile j does not affect SBUF[i] for i ≠ j
-/
import Mathlib

namespace Pythia.Numerical.MemoryTileIdentity

/-! ### State model -/

/-- Joint state of the SBUF (scratchpad) and HBM memories.
    `n` is the number of tile slots; `α` is the tile-data type. -/
structure SBUFState (n : ℕ) (α : Type*) where
  sbuf : Fin n → α
  hbm  : Fin n → α

/-! ### Operations -/

/-- Load tile `i` from HBM into SBUF. All other slots are unchanged. -/
def sbufLoad {n : ℕ} {α : Type*} (s : SBUFState n α) (i : Fin n) : SBUFState n α :=
  { s with sbuf := Function.update s.sbuf i (s.hbm i) }

/-- Write value `v` to HBM slot `i`. All other HBM slots are unchanged. -/
def hbmWrite {n : ℕ} {α : Type*} (s : SBUFState n α) (i : Fin n) (v : α) : SBUFState n α :=
  { s with hbm := Function.update s.hbm i v }

/-- Write value `v` to SBUF slot `i`. All other SBUF slots are unchanged. -/
def sbufWrite {n : ℕ} {α : Type*} (s : SBUFState n α) (i : Fin n) (v : α) : SBUFState n α :=
  { s with sbuf := Function.update s.sbuf i v }

/-! ### Theorem 1 — load stores the tile -/

/-- After loading tile `i`, SBUF[i] equals HBM[i]. -/
theorem sbuf_load_stores_tile {n : ℕ} {α : Type*} (s : SBUFState n α) (i : Fin n) :
    (sbufLoad s i).sbuf i = (sbufLoad s i).hbm i := by
  simp [sbufLoad, Function.update_self]

/-! ### Theorem 2 — reuse is sound when HBM is unchanged -/

/-- If HBM[i] has not changed since tile `i` was loaded (i.e.
    the current HBM[i] still equals the value that was loaded into SBUF[i]),
    then reading SBUF[i] gives the same result as HBM[i].

    Concretely: if `s₁ = sbufLoad s₀ i` and later `s₂.hbm i = s₁.hbm i`
    and `s₂.sbuf i = s₁.sbuf i`, then `s₂.sbuf i = s₂.hbm i`. -/
theorem sbuf_reuse_eq_load {n : ℕ} {α : Type*}
    (s₀ s₂ : SBUFState n α) (i : Fin n)
    (h_sbuf : s₂.sbuf i = (sbufLoad s₀ i).sbuf i)
    (h_hbm  : s₂.hbm  i = (sbufLoad s₀ i).hbm  i) :
    s₂.sbuf i = s₂.hbm i := by
  rw [h_sbuf, h_hbm]
  simp [sbufLoad, Function.update_self]

/-! ### Theorem 3 — no SBUF write preserves SBUF[i] -/

/-- If no write to SBUF slot `i` has occurred, the slot value is unchanged.

    Formally: a write to slot `j ≠ i` leaves SBUF[i] intact. -/
theorem no_write_preserves_sbuf {n : ℕ} {α : Type*}
    (s : SBUFState n α) (i j : Fin n) (v : α) (h : i ≠ j) :
    (sbufWrite s j v).sbuf i = s.sbuf i := by
  simp only [sbufWrite]
  exact Function.update_of_ne h v s.sbuf

/-! ### Theorem 4 — redundant load elimination -/

/-- Loading tile `i` twice, with no intervening HBM write to `i`,
    produces the same SBUF state as loading once.

    `sbufLoad (sbufLoad s i) i = sbufLoad s i` -/
theorem redundant_load_elimination {n : ℕ} {α : Type*}
    (s : SBUFState n α) (i : Fin n) :
    sbufLoad (sbufLoad s i) i = sbufLoad s i := by
  simp only [sbufLoad]
  congr 1
  exact Function.update_idem (s.hbm i) (s.hbm i) s.sbuf

/-! ### Theorem 5 — SBUF isolation across tile indices -/

/-- Loading tile `j` does not affect SBUF[i] for `i ≠ j`. -/
theorem sbuf_isolation {n : ℕ} {α : Type*}
    (s : SBUFState n α) (i j : Fin n) (h : i ≠ j) :
    (sbufLoad s j).sbuf i = s.sbuf i := by
  simp only [sbufLoad]
  exact Function.update_of_ne h (s.hbm j) s.sbuf

end Pythia.Numerical.MemoryTileIdentity
