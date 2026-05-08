/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# INT8 Symmetric Quantization Round-Trip Error Bound

Symmetric INT8 quantization maps a real value `x` to a signed 8-bit
integer and back:

  scale  := max|x_range| / 127          (step size, > 0)
  quant(x)    := round(x / scale)       clamped to [-128, 127]
  dequant(q)  := q * scale

The round-trip error comes from the rounding step:

  |dequant(quant(x)) - x| = |round(x/scale) * scale - x| ≤ scale / 2

## Proof outline

1. `round_error` — For any real `x`, `|x - round x| ≤ 1/2`.
   This is `abs_sub_round` from Mathlib's `Mathlib.Algebra.Order.Round`.

2. `quant_dequant_error` — For `scale > 0` and any `x : ℝ`,
   `|⌊x/scale + 1/2⌋ * scale - x| ≤ scale / 2`.
   Proof: substitute `y := x / scale`, so the LHS becomes
   `|round(y) * scale - y * scale| = scale * |round(y) - y|`
   ≤ scale * (1/2) = scale/2.

3. `quant_preserves_zero` — `round(0 / scale) = 0`.

4. `dequant_quant_bound` — The full bound in terms of the named
   `quant` and `dequant` functions.

## Key Mathlib lemmas used

* `abs_sub_round  : |x - round x| ≤ 1 / 2`   (Mathlib.Algebra.Order.Round)
* `round_eq       : round x = ⌊x + 1/2⌋`      (LinearOrderedField)
* `Int.floor_le`, `Int.lt_floor_add_one`       (floor bounds)

## Main results

* `round_error`         — `|x - round x| ≤ 1 / 2`
* `quant_dequant_error` — `|⌊x/scale + 1/2⌋ * scale - x| ≤ scale / 2`
* `quant_preserves_zero`— `(round (0 / scale) : ℤ) = 0`
* `dequant_quant_bound` — `|dequant (quant scale x) - x| ≤ scale / 2`
-/
import Mathlib

namespace Pythia.Numerical.INT8Quantization

open Int

noncomputable section

/-! ### Quantization primitives -/

/-- INT8 quantization of a real value `x` at step size `scale`:
    round `x / scale` to the nearest integer.
    (Clamping to [-128, 127] is omitted; it can only reduce the error.) -/
def quant (scale x : ℝ) : ℤ := round (x / scale)

/-- INT8 dequantization: multiply the integer code back by `scale`. -/
def dequant (scale : ℝ) (q : ℤ) : ℝ := q * scale

/-! ### Core lemmas -/

/-- **Round error.** For any real `x`, the nearest-integer rounding error
is at most `1/2`. This is the standard half-ULP bound for scalar rounding.

`round x` is defined in Mathlib as `⌊x + 1/2⌋` (ties round up), which
gives `x - 1/2 < round x ≤ x + 1/2`, i.e. `|x - round x| ≤ 1/2`. -/
theorem round_error (x : ℝ) : |x - round x| ≤ 1 / 2 := by
  have h := abs_sub_round x
  linarith [h]

/-- **Quant-dequant error.** For any real `x` and `scale > 0`,
the round-trip error satisfies
  `|⌊x/scale + 1/2⌋ * scale - x| ≤ scale / 2`.

Proof: let `y = x / scale`.  Then
  `⌊y + 1/2⌋ * scale - x`
  `= round(y) * scale - y * scale`
  `= (round(y) - y) * scale`,
so
  `|⌊x/scale + 1/2⌋ * scale - x| = |round(y) - y| * scale ≤ (1/2) * scale`. -/
theorem quant_dequant_error (scale x : ℝ) (hscale : 0 < scale) :
    |(⌊x / scale + 1 / 2⌋ : ℤ) * scale - x| ≤ scale / 2 := by
  -- Use round_eq: round(y) = ⌊y + 1/2⌋
  have hround : (⌊x / scale + 1 / 2⌋ : ℤ) = round (x / scale) := by
    rw [round_eq]
  rw [hround]
  -- Cast round to ℝ and rewrite
  -- Rewrite: |round(y) * scale - x| = |round(y) - y| * scale
  have habs : |(round (x / scale) : ℝ) * scale - x|
      = |(round (x / scale) : ℝ) - x / scale| * scale := by
    have : (round (x / scale) : ℝ) * scale - x =
        ((round (x / scale) : ℝ) - x / scale) * scale := by
      field_simp
    rw [this, abs_mul, abs_of_pos hscale]
  rw [habs]
  -- Bound |round(y) - y| ≤ 1/2 and multiply by scale
  have herr : |(round (x / scale) : ℝ) - x / scale| ≤ 1 / 2 := by
    have := abs_sub_round (x / scale)
    rw [abs_sub_comm]
    exact this
  have hle := mul_le_mul_of_nonneg_right herr hscale.le
  linarith

/-- **Quantization preserves zero.**
When `scale > 0`, quantizing `0` gives the integer code `0`. -/
theorem quant_preserves_zero (scale : ℝ) (_hscale : 0 < scale) :
    quant scale 0 = 0 := by
  simp [quant, zero_div]

/-- **Full round-trip error bound.**
For any real `x` and `scale > 0`,
  `|dequant(quant(scale, x)) - x| ≤ scale / 2`.

This is the main INT8 quantization error theorem: symmetric INT8
quantization at step size `scale` introduces at most a half-step error. -/
theorem dequant_quant_bound (scale x : ℝ) (hscale : 0 < scale) :
    |dequant scale (quant scale x) - x| ≤ scale / 2 := by
  -- Unfold definitions
  simp only [dequant, quant]
  -- Now the goal is |↑(round (x / scale)) * scale - x| ≤ scale / 2
  -- Use round_eq to rewrite round as floor
  have hround : (round (x / scale) : ℝ) * scale - x =
      (⌊x / scale + 1 / 2⌋ : ℤ) * scale - x := by
    congr 1
    norm_cast
    rw [round_eq]
  rw [hround]
  exact quant_dequant_error scale x hscale

end

end Pythia.Numerical.INT8Quantization
