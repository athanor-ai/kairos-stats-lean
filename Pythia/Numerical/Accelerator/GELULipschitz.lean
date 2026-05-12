/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GELU Activation: Lipschitz Continuity

The tanh-approximate GELU activation used in accelerator kernels is

  gelu_approx(x) = (1/2) · x · (1 + tanh(√(2/π) · (x + 0.044715 · x³)))

## Main results

* `gelu_approx_zero`             — gelu_approx 0 = 0
* `gelu_approx_pos_of_pos`       — x > 0 → gelu_approx x > 0
* `gelu_approx_nonneg_of_nonneg` — x ≥ 0 → gelu_approx x ≥ 0
* `gelu_approx_differentiable`   — everywhere differentiable
* `gelu_approx_lipschitz`        — LipschitzWith 2 gelu_approx

## Proof strategy

Derivative: D(x) = (1/2)·(1+t) + (1/2)·x·(1−t²)·u′ where t = tanh(tanh_arg x).
1. tanh_arg is odd → D(x) + D(−x) = 1.
2. x ≥ 0 → D(x) ∈ [0, 2]:
   • ≥ 0: both summands nonneg.
   • ≤ 2: 1−tanh(u) ≤ 2·exp(−2u) (from definition), 4-term Taylor for exp,
     and 3·0.044715·π < 4/3 (from pi_lt_d4: π < 3.1416).
3. x ≤ 0 → D(x) = 1 − D(−x) ∈ [−1, 1].
-/
import Mathlib

open Real NNReal

namespace Pythia.Numerical.GELULipschitz

/-! ### Local tanh derivative (mirrors SoftcapLipschitz) -/

private theorem hasDerivAt_tanh' (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hq : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  rw [show (fun y => Real.sinh y / Real.cosh y) = Real.tanh from
    funext fun y => (Real.tanh_eq_sinh_div_cosh y).symm] at hq
  convert hq using 1
  have hid : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by
    linarith [Real.cosh_sq_sub_sinh_sq x]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

private theorem differentiable_tanh' : Differentiable ℝ Real.tanh :=
  fun x => (hasDerivAt_tanh' x).differentiableAt

/-! ### Definitions -/

noncomputable def tanh_arg (x : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3)

noncomputable def gelu_approx (x : ℝ) : ℝ :=
  (1 / 2) * x * (1 + Real.tanh (tanh_arg x))

/-! ### Basic values -/

theorem gelu_approx_zero : gelu_approx 0 = 0 := by simp [gelu_approx, tanh_arg]

theorem gelu_approx_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < gelu_approx x :=
  mul_pos (mul_pos (by norm_num) hx) (by linarith [Real.neg_one_lt_tanh (tanh_arg x)])

theorem gelu_approx_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gelu_approx x :=
  mul_nonneg (mul_nonneg (by norm_num) hx) (by linarith [Real.neg_one_lt_tanh (tanh_arg x)])

/-! ### Differentiability -/

private theorem tanh_arg_differentiable : Differentiable ℝ tanh_arg :=
  (differentiable_const _).mul
    (differentiable_id.add ((differentiable_id.pow 3).const_mul _))

theorem gelu_approx_differentiable : Differentiable ℝ gelu_approx :=
  ((differentiable_const _).mul differentiable_id).mul
    ((differentiable_const _).add (differentiable_tanh'.comp tanh_arg_differentiable))

/-! ### Derivative formula -/

private theorem hasDerivAt_tanh_arg (x : ℝ) :
    HasDerivAt tanh_arg (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)) x := by
  unfold tanh_arg
  have h3 : HasDerivAt (fun y : ℝ => 0.044715 * y ^ 3) (0.044715 * (3 * x ^ 2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul 0.044715
  have hinner : HasDerivAt (fun y : ℝ => y + 0.044715 * y ^ 3) (1 + 0.044715 * (3 * x ^ 2)) x :=
    (hasDerivAt_id x).add h3
  have h := hinner.const_mul (Real.sqrt (2 / Real.pi))
  convert h using 1; ring

theorem hasDerivAt_gelu_approx (x : ℝ) :
    HasDerivAt gelu_approx
      ((1 / 2) * (1 + Real.tanh (tanh_arg x)) +
        (1 / 2) * x * ((1 - Real.tanh (tanh_arg x) ^ 2) *
          (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)))) x := by
  unfold gelu_approx
  have htc : HasDerivAt (fun y => Real.tanh (tanh_arg y))
      ((1 - Real.tanh (tanh_arg x) ^ 2) *
        (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2))) x :=
    (hasDerivAt_tanh' _).comp x (hasDerivAt_tanh_arg x)
  have hg : HasDerivAt (fun y => (1 : ℝ) + Real.tanh (tanh_arg y))
      (0 + (1 - Real.tanh (tanh_arg x) ^ 2) *
        (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2))) x :=
    (hasDerivAt_const x 1).add htc
  have hf : HasDerivAt (fun y : ℝ => (1 / 2) * y) (1 / 2 * 1) x :=
    (hasDerivAt_id x).const_mul _
  have hprod : HasDerivAt (fun y => (1 / 2) * y * ((1 : ℝ) + Real.tanh (tanh_arg y)))
      ((1 / 2 * 1) * (1 + Real.tanh (tanh_arg x)) +
       (1 / 2) * x * (0 + (1 - Real.tanh (tanh_arg x) ^ 2) *
         (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)))) x :=
    hf.mul hg
  convert hprod using 1; ring

/-! ### Analytic lemmas -/

private theorem tanh_arg_neg (x : ℝ) : tanh_arg (-x) = -tanh_arg x := by
  unfold tanh_arg; ring

/-- 1 − tanh u ≤ 2·exp(−2u) for u ≥ 0. -/
private theorem one_sub_tanh_le (u : ℝ) (hu : 0 ≤ u) :
    1 - Real.tanh u ≤ 2 * Real.exp (-2 * u) := by
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  -- 1 - tanh(u) = (cosh(u) - sinh(u)) / cosh(u) = exp(-u) / cosh(u).
  have hrw : 1 - Real.tanh u = Real.exp (-u) / Real.cosh u := by
    have hcs := Real.cosh_sub_sinh u
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    linarith
  rw [hrw]
  -- exp(-u)/cosh(u) ≤ 2*exp(-2u) iff exp(-u) ≤ 2*exp(-2u)*cosh(u).
  rw [div_le_iff₀ hc]
  -- 2*exp(-2u)*cosh(u) = 2*exp(-2u)*(exp(u)+exp(-u))/2 = exp(-u)+exp(-3u) ≥ exp(-u).
  have h1 : Real.exp (-2 * u) * Real.exp u = Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-2 * u) * Real.exp (-u) = Real.exp (-3 * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.cosh_eq, show 2 * Real.exp (-2 * u) * ((Real.exp u + Real.exp (-u)) / 2) =
    Real.exp (-2 * u) * Real.exp u + Real.exp (-2 * u) * Real.exp (-u) by ring]
  rw [h1, h2]
  linarith [Real.exp_pos (-3 * u)]

private theorem c3pi_lt : 3 * 0.044715 * Real.pi < 4 / 3 := by
  nlinarith [Real.pi_lt_d4]

private theorem deriv_add_neg (x : ℝ) :
    ((1 / 2) * (1 + Real.tanh (tanh_arg x)) +
     (1 / 2) * x * ((1 - Real.tanh (tanh_arg x) ^ 2) *
       (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)))) +
    ((1 / 2) * (1 + Real.tanh (tanh_arg (-x))) +
     (1 / 2) * (-x) * ((1 - Real.tanh (tanh_arg (-x)) ^ 2) *
       (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * (-x) ^ 2)))) = 1 := by
  rw [tanh_arg_neg, Real.tanh_neg]; ring

private theorem deriv_nonneg_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (1 / 2) * (1 + Real.tanh (tanh_arg x)) +
        (1 / 2) * x * ((1 - Real.tanh (tanh_arg x) ^ 2) *
          (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2))) :=
  add_nonneg
    (mul_nonneg (by norm_num) (by linarith [Real.neg_one_lt_tanh (tanh_arg x)]))
    (mul_nonneg (mul_nonneg (by norm_num) hx)
      (mul_nonneg (by nlinarith [Real.tanh_sq_lt_one (tanh_arg x)])
        (mul_nonneg (Real.sqrt_nonneg _) (by nlinarith [sq_nonneg x]))))

private theorem deriv_le_two_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    (1 / 2) * (1 + Real.tanh (tanh_arg x)) +
    (1 / 2) * x * ((1 - Real.tanh (tanh_arg x) ^ 2) *
      (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2))) ≤ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- a = √(2/π) · x ≥ 0; note a² = (2/π)·x² so x² = a²·π/2.
  have hsq : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi := Real.sq_sqrt (by positivity)
  set a := Real.sqrt (2 / Real.pi) * x with ha_def
  have ha : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) hx
  have ha_sq : a ^ 2 = 2 / Real.pi * x ^ 2 := by
    simp only [ha_def, mul_pow]; rw [hsq]
  have hx_sq : x ^ 2 = a ^ 2 * (Real.pi / 2) := by
    have := ha_sq; field_simp at this ⊢; linarith
  -- u = tanh_arg x ≥ a ≥ 0.
  have hu_ge_a : a ≤ tanh_arg x := by
    unfold tanh_arg
    nlinarith [sq_nonneg x, mul_nonneg (Real.sqrt_nonneg (2 / Real.pi)) (sq_nonneg x)]
  have hu_nn : 0 ≤ tanh_arg x := le_trans ha hu_ge_a
  -- t = tanh(tanh_arg x); basic bounds.
  have ht1 : Real.tanh (tanh_arg x) < 1 := Real.tanh_lt_one _
  have ht_neg1 : -1 < Real.tanh (tanh_arg x) := Real.neg_one_lt_tanh _
  have h1t : 0 ≤ 1 - Real.tanh (tanh_arg x) := by linarith
  have h1t2 : 0 ≤ 1 - Real.tanh (tanh_arg x) ^ 2 := by
    nlinarith [Real.tanh_sq_lt_one (tanh_arg x)]
  -- 1 − t ≤ 2·exp(−2·tanh_arg x) ≤ 2·exp(−2a).
  have h1t_le : 1 - Real.tanh (tanh_arg x) ≤ 2 * Real.exp (-2 * a) := by
    have step1 := one_sub_tanh_le (tanh_arg x) hu_nn
    have step2 : Real.exp (-2 * tanh_arg x) ≤ Real.exp (-2 * a) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.exp_nonneg (-2 * tanh_arg x))]
  -- 4-term Taylor: 1 + 2a + 2a² + (4/3)a³ ≤ exp(2a).
  have htaylor : 1 + 2 * a + 2 * a ^ 2 + (4 / 3) * a ^ 3 ≤ Real.exp (2 * a) := by
    have h := Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
               pow_succ, pow_zero, Nat.cast_one] at h
    push_cast at h; nlinarith
  -- (1+2a+2a²+(4/3)a³)·exp(−2a) ≤ 1.
  have hprod1 : (1 + 2 * a + 2 * a ^ 2 + (4 / 3) * a ^ 3) * Real.exp (-2 * a) ≤ 1 := by
    have he : Real.exp (2 * a) * Real.exp (-2 * a) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    nlinarith [Real.exp_pos (2 * a), Real.exp_nonneg (-2 * a)]
  -- Polynomial: 2·a·(1 + 0.044715·3·x²) ≤ 1 + 2a + 2a² + (4/3)a³.
  have hpoly : 2 * a * (1 + 0.044715 * 3 * x ^ 2) ≤ 1 + 2 * a + 2 * a ^ 2 + (4 / 3) * a ^ 3 := by
    rw [hx_sq]
    nlinarith [c3pi_lt, mul_nonneg ha (mul_nonneg ha ha), sq_nonneg a]
  -- 2·exp(−2a)·a·(1 + 0.044715·3·x²) ≤ 1.
  have hbound : 2 * Real.exp (-2 * a) * (a * (1 + 0.044715 * 3 * x ^ 2)) ≤ 1 := by
    have hea := Real.exp_nonneg (-2 * a)
    have hau : 0 ≤ a * (1 + 0.044715 * 3 * x ^ 2) :=
      mul_nonneg ha (by nlinarith [sq_nonneg x])
    nlinarith
  -- x · u' = a · (1 + 0.044715·3·x²).
  have hxu' : x * (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)) =
      a * (1 + 0.044715 * 3 * x ^ 2) := by
    show x * (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)) =
        Real.sqrt (2 / Real.pi) * x * (1 + 0.044715 * 3 * x ^ 2)
    ring
  -- 1 - t² = (1-t)·(1+t) ≤ 2·(1-t) since 1+t ≤ 2.
  have h1t2_le : 1 - Real.tanh (tanh_arg x) ^ 2 ≤ 2 * (1 - Real.tanh (tanh_arg x)) := by
    nlinarith
  -- Final bound.
  have hu'_nn : 0 ≤ Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (by nlinarith [sq_nonneg x])
  nlinarith [mul_nonneg h1t2 hu'_nn, Real.exp_nonneg (-2 * a),
             mul_nonneg ha (by nlinarith [sq_nonneg x] : 0 ≤ 1 + 0.044715 * 3 * x ^ 2)]

/-! ### NNNorm bound on the derivative -/

private theorem nnnorm_deriv_le (x : ℝ) :
    ‖(1 / 2) * (1 + Real.tanh (tanh_arg x)) +
      (1 / 2) * x * ((1 - Real.tanh (tanh_arg x) ^ 2) *
        (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)))‖₊ ≤ 2 := by
  set D := (1 / 2) * (1 + Real.tanh (tanh_arg x)) +
    (1 / 2) * x * ((1 - Real.tanh (tanh_arg x) ^ 2) *
      (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * x ^ 2)))
  -- Define the "companion" derivative at -x; it plus D equals 1.
  set D' := (1 / 2) * (1 + Real.tanh (tanh_arg (-x))) +
    (1 / 2) * (-x) * ((1 - Real.tanh (tanh_arg (-x)) ^ 2) *
      (Real.sqrt (2 / Real.pi) * (1 + 0.044715 * 3 * (-x) ^ 2)))
  have hDD' : D + D' = 1 := deriv_add_neg x
  have habs : |D| ≤ 2 := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- D ≥ -2.
      rcases lt_or_ge x 0 with hx | hx
      · have hx' : 0 ≤ -x := le_of_lt (neg_pos.mpr hx)
        have hD'_le : D' ≤ 2 := deriv_le_two_of_nonneg (-x) hx'
        linarith
      · have hD_nn : 0 ≤ D := deriv_nonneg_of_nonneg x hx
        linarith
    · -- D ≤ 2.
      rcases lt_or_ge x 0 with hx | hx
      · have hx' : 0 ≤ -x := le_of_lt (neg_pos.mpr hx)
        have hD'_nn : 0 ≤ D' := deriv_nonneg_of_nonneg (-x) hx'
        linarith
      · exact deriv_le_two_of_nonneg x hx
  have h : (‖D‖₊ : ℝ) ≤ 2 := by
    rw [coe_nnnorm, Real.norm_eq_abs]
    exact habs
  exact_mod_cast h

/-! ### Main Lipschitz theorem -/

theorem gelu_approx_lipschitz : LipschitzWith 2 gelu_approx :=
  lipschitzWith_of_nnnorm_deriv_le gelu_approx_differentiable
    fun x => (hasDerivAt_gelu_approx x).deriv ▸ nnnorm_deriv_le x

end Pythia.Numerical.GELULipschitz
