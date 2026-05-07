/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Logit Softcapping is 1-Lipschitz

Logit softcapping (Gemma 2, arXiv:2408.00118) clips logits via

  softcap(t, x) = t · tanh(x / t)

where `t > 0` is the cap parameter.  This file proves that for any fixed
`t > 0` the map `x ↦ softcap(t, x)` is 1-Lipschitz:

  |softcap(t, x) - softcap(t, y)| ≤ |x - y|

## Proof outline

1. **Derivative of `tanh`**: quotient rule on `sinh / cosh` gives
   `HasDerivAt Real.tanh (1 - tanh(x)²) x`.
2. **Derivative norm ≤ 1**: since `tanh(x)² < 1` we get
   `0 ≤ 1 - tanh(x)² ≤ 1`, so `‖deriv tanh x‖₊ ≤ 1`.
3. **`tanh` is 1-Lipschitz**: by `lipschitzWith_of_nnnorm_deriv_le` (MVT).
4. **Softcap bound**:
     |t · tanh(x/t) - t · tanh(y/t)|
       = t · |tanh(x/t) - tanh(y/t)|
       ≤ t · |x/t - y/t|     (1-Lipschitz of tanh)
       = |x - y|

## Main results

* `Real.hasDerivAt_tanh`      — derivative of tanh at every real point
* `Real.differentiable_tanh`  — tanh is everywhere differentiable
* `Real.lipschitzWith_tanh`   — tanh is 1-Lipschitz
* `softcap`                   — the softcap function
* `softcap_lipschitz`         — `LipschitzWith 1 (softcap t)` for `t > 0`
* `softcap_abs_sub_le`        — pointwise `|softcap t x - softcap t y| ≤ |x - y|`
-/
import Mathlib

namespace Real

/-! ### Derivative of `Real.tanh` -/

/-- `Real.tanh` has derivative `1 - tanh(x)²` at every real point.
    Proof: `tanh = sinh / cosh`; quotient rule gives
    `(cosh·cosh - sinh·sinh) / cosh² = 1 / cosh²`, and
    `tanh² = sinh²/cosh²` so `1 - tanh² = (cosh²-sinh²)/cosh² = 1/cosh²`. -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  -- Apply the quotient rule to sinh/cosh
  have hq : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  -- The function sinh/cosh equals tanh
  have htanh : (fun y => Real.sinh y / Real.cosh y) = Real.tanh :=
    funext fun y => (Real.tanh_eq_sinh_div_cosh y).symm
  -- The derivative value equals 1 - tanh²
  have hval : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
      1 - Real.tanh x ^ 2 := by
    have hid : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by
      have := Real.cosh_sq_sub_sinh_sq x; linarith [this]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [htanh] at hq
  rwa [hval] at hq

/-- `Real.tanh` is differentiable everywhere. -/
theorem differentiable_tanh : Differentiable ℝ Real.tanh :=
  fun x => (hasDerivAt_tanh x).differentiableAt

/-- The `deriv` of `Real.tanh` equals `1 - tanh²`. -/
@[simp]
theorem deriv_tanh' : deriv Real.tanh = fun x => 1 - Real.tanh x ^ 2 :=
  funext fun x => (hasDerivAt_tanh x).deriv

/-! ### `tanh` is 1-Lipschitz -/

/-- `tanh` is 1-Lipschitz. -/
theorem lipschitzWith_tanh : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_tanh
  intro x
  simp only [deriv_tanh']
  have h0 : (0 : ℝ) ≤ 1 - Real.tanh x ^ 2 :=
    sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x))
  rw [Real.nnnorm_of_nonneg h0]
  exact_mod_cast sub_le_self 1 (sq_nonneg (Real.tanh x))

end Real

/-! ### Softcap definition and Lipschitz property -/

namespace Pythia.Numerical.Accelerator

/-- Logit softcapping with cap parameter `t`:
    `softcap t x = t · tanh(x / t)`.
    For `t > 0` this maps ℝ into the open interval `(-t, t)`
    while being 1-Lipschitz. -/
noncomputable def softcap (t : ℝ) (x : ℝ) : ℝ := t * Real.tanh (x / t)

/-- For `t > 0`, `softcap t` is 1-Lipschitz. -/
theorem softcap_lipschitz {t : ℝ} (ht : 0 < t) : LipschitzWith 1 (softcap t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [softcap, Real.dist_eq, NNReal.coe_one, one_mul]
  rw [show t * Real.tanh (x / t) - t * Real.tanh (y / t) =
      t * (Real.tanh (x / t) - Real.tanh (y / t)) by ring]
  rw [abs_mul, abs_of_pos ht]
  -- Use 1-Lipschitz of tanh: |tanh a - tanh b| ≤ dist a b = |a - b|
  have htanh : |Real.tanh (x / t) - Real.tanh (y / t)| ≤ |x / t - y / t| := by
    have h := Real.lipschitzWith_tanh.dist_le_mul (x / t) (y / t)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    exact h
  have hscale : |x / t - y / t| = |x - y| / t := by
    rw [show x / t - y / t = (x - y) / t by ring, abs_div, abs_of_pos ht]
  rw [hscale] at htanh
  calc t * |Real.tanh (x / t) - Real.tanh (y / t)|
      ≤ t * (|x - y| / t) := mul_le_mul_of_nonneg_left htanh ht.le
    _ = |x - y| := by field_simp

/-- Pointwise form: `|softcap t x - softcap t y| ≤ |x - y|` for `t > 0`. -/
theorem softcap_abs_sub_le {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |softcap t x - softcap t y| ≤ |x - y| := by
  have h := (softcap_lipschitz ht).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact h

end Pythia.Numerical.Accelerator
