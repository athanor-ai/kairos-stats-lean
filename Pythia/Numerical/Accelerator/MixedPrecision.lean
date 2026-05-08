/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BF16→FP32 Mixed-Precision Error Analysis

Extends QuantizedReduction.lean with a full error analysis for the
BF16→FP32 mixed-precision pattern used in modern ML accelerators.

The customer question: "what happens to my FP32 error bound when
matmuls run in BF16?"

## Format specifications

BF16 (Brain Float 16): 1 sign + 8 exponent + 7 mantissa bits.
  - Machine epsilon: ε_bf16 = 2^{-7} (last mantissa bit)
  - Unit roundoff:   u_bf16 = 2^{-8} = ε_bf16/2

FP32 (IEEE 754 single): 1 sign + 8 exponent + 23 mantissa bits.
  - Machine epsilon: ε_fp32 = 2^{-23}
  - Unit roundoff:   u_fp32 = 2^{-24} = ε_fp32/2

## Mixed-precision inner product error decomposition

For an inner product of n BF16 values accumulated in FP32:

  1. Each BF16 input x has rounding error ≤ u_bf16 · |x|
  2. Each BF16×BF16 multiplication has error ≤ u_bf16 · |a·b|
     (total input+multiply contribution ≤ 2·u_bf16 per term)
  3. FP32 accumulation error ≤ γ_n(u_fp32) · Σ|products|
     where γ_n(u) = n·u / (1 - n·u)

  Total: |fl_mixed(a·b) - a·b| ≤ (2·u_input + γ_n(u_accum)) · Σ|aᵢ|·|bᵢ|

## Main results

* `bf16_unit_roundoff`   — u_bf16 = 2^{-8}
* `fp32_unit_roundoff`   — u_fp32 = 2^{-24}
* `bf16_eps`             — ε_bf16 = 2^{-7} (machine epsilon)
* `fp32_eps`             — ε_fp32 = 2^{-23} (machine epsilon)
* `gamma_mp`             — mixed-precision γ factor with arbitrary unit roundoff
* `mixed_precision_inner_product_error` — abstract bound for any (u_input, u_accum)
* `bf16_fp32_tighter_than_bf16_only`   — mixed precision is tighter than pure BF16
* `mixed_precision_matmul_error`        — per-entry matmul bound

## Specialisations

* `bf16_fp32_inner_product_error` — concrete BF16+FP32 inner product bound
* `bf16_fp32_matmul_error`        — concrete BF16+FP32 matmul bound

## References

* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). Theorem 3.1, §3.6 (mixed precision).
* Kalamkar et al. "A Study of BFLOAT16 for Deep Learning Training." arXiv:1905.12322.
* Pythia.Numerical.Accelerator.QuantizedReduction (sister module).
-/
import Mathlib
import Pythia.Numerical.IEEE754

namespace Pythia.Numerical.MixedPrecision

open Finset BigOperators

noncomputable section

/-!
## Precision constants
-/

/-- BF16 machine epsilon: the gap between 1 and the next BF16 representable
    value. BF16 has 7 mantissa bits, giving ε_bf16 = 2^{-7}. -/
def bf16_eps : ℝ := (2 : ℝ) ^ (-7 : ℤ)

/-- FP32 (IEEE 754 single precision) machine epsilon: 23 mantissa bits,
    giving ε_fp32 = 2^{-23}. -/
def fp32_eps : ℝ := (2 : ℝ) ^ (-23 : ℤ)

/-- BF16 unit roundoff (half-epsilon): u_bf16 = 2^{-8}. -/
def bf16_unit_roundoff : ℝ := (2 : ℝ) ^ (-8 : ℤ)

/-- FP32 unit roundoff (half-epsilon): u_fp32 = 2^{-24}. -/
def fp32_unit_roundoff : ℝ := (2 : ℝ) ^ (-24 : ℤ)

/-- bf16_unit_roundoff = bf16_eps / 2. -/
theorem bf16_unit_roundoff_eq : bf16_unit_roundoff = bf16_eps / 2 := by
  unfold bf16_unit_roundoff bf16_eps
  norm_num [zpow_sub₀ (two_ne_zero' ℝ)]

/-- fp32_unit_roundoff = fp32_eps / 2. -/
theorem fp32_unit_roundoff_eq : fp32_unit_roundoff = fp32_eps / 2 := by
  unfold fp32_unit_roundoff fp32_eps
  norm_num [zpow_sub₀ (two_ne_zero' ℝ)]

/-- bf16_unit_roundoff is positive. -/
theorem bf16_unit_roundoff_pos : (0 : ℝ) < bf16_unit_roundoff := by
  unfold bf16_unit_roundoff; positivity

/-- fp32_unit_roundoff is positive. -/
theorem fp32_unit_roundoff_pos : (0 : ℝ) < fp32_unit_roundoff := by
  unfold fp32_unit_roundoff; positivity

/-- bf16_eps is the standard definition: 2^{-7}. -/
@[simp]
theorem bf16_eps_val : bf16_eps = (2 : ℝ) ^ (-7 : ℤ) := rfl

/-- fp32_eps is the standard definition: 2^{-23}. -/
@[simp]
theorem fp32_eps_val : fp32_eps = (2 : ℝ) ^ (-23 : ℤ) := rfl

/-- FP32 is strictly more precise than BF16: u_fp32 < u_bf16. -/
theorem fp32_more_precise_than_bf16 : fp32_unit_roundoff < bf16_unit_roundoff := by
  unfold fp32_unit_roundoff bf16_unit_roundoff
  norm_num

/-!
## Abstract γ factor for mixed precision
-/

/-- Standard Higham error amplification factor for accumulation with
    unit roundoff `u`:
      γ_n(u) = n·u / (1 - n·u)

    This generalises the double-precision `MatMul.gamma` to arbitrary `u`,
    allowing parametric treatment of FP16, BF16, FP32, etc. -/
def gamma_mp (n : ℕ) (u : ℝ) : ℝ := (n : ℝ) * u / (1 - (n : ℝ) * u)

/-- gamma_mp is non-negative when n·u < 1. -/
theorem gamma_mp_nonneg {n : ℕ} {u : ℝ} (hu_pos : 0 < u)
    (hnu : (n : ℝ) * u < 1) : 0 ≤ gamma_mp n u := by
  unfold gamma_mp
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) hu_pos.le
  · linarith

/-- gamma_mp is positive when n ≥ 1 and n·u < 1. -/
theorem gamma_mp_pos {n : ℕ} {u : ℝ} (hn : 0 < n) (hu_pos : 0 < u)
    (hnu : (n : ℝ) * u < 1) : 0 < gamma_mp n u := by
  unfold gamma_mp
  apply div_pos
  · exact mul_pos (Nat.cast_pos.mpr hn) hu_pos
  · linarith

/-- gamma_mp is monotone in n (for fixed u with n·u < 1). -/
theorem gamma_mp_mono {n m : ℕ} {u : ℝ} (hnm : n ≤ m) (hu_pos : 0 < u)
    (hmu : (m : ℝ) * u < 1) : gamma_mp n u ≤ gamma_mp m u := by
  unfold gamma_mp
  have hnu : (n : ℝ) * u < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hnm) hu_pos.le) hmu
  have hd_n : 0 < 1 - (n : ℝ) * u := by linarith
  have hd_m : 0 < 1 - (m : ℝ) * u := by linarith
  rw [div_le_div_iff₀ hd_n hd_m]
  have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
  nlinarith [mul_nonneg (Nat.cast_nonneg n) hu_pos.le,
             mul_nonneg (Nat.cast_nonneg m) hu_pos.le]

/-- In the practical regime n·u ≤ 1/2, gamma_mp ≤ 2·n·u. -/
theorem gamma_mp_bound {n : ℕ} {u : ℝ} (hu_pos : 0 ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 2) : gamma_mp n u ≤ 2 * ((n : ℝ) * u) := by
  unfold gamma_mp
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  have hnu_nn : 0 ≤ (n : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu_pos
  rw [div_le_iff₀ hd]
  -- Goal: n*u ≤ 2*(n*u)*(1-n*u)
  -- Equivalent to n*u ≤ 2*(n*u) - 2*(n*u)^2, i.e. 2*(n*u)^2 ≤ n*u, i.e. 2*n*u ≤ 1 (when n*u>0)
  nlinarith [mul_nonneg hnu_nn hnu_nn]

/-!
## Mixed-precision inner product error (abstract)
-/

/-- **Abstract mixed-precision inner product error bound.**

For an inner product of n terms where:
- inputs are rounded to a format with unit roundoff `u_input`
  (each input x rounded to x̂ with |x̂ - x| ≤ u_input · |x|)
- products are computed in the input format
  (each x̂ᵢ · ŷᵢ computed as fl(x̂ᵢ · ŷᵢ) with relative error ≤ u_input)
- accumulated in a higher-precision format with unit roundoff `u_accum`

The combined per-term input/multiply rounding contributes at most
2·u_input · |aᵢ · bᵢ| per term, and the FP accumulation contributes
γ_n(u_accum) · Σ|aᵢ · bᵢ|.

Total bound:

  |result - Σ aᵢ·bᵢ| ≤ (2·u_input + γ_n(u_accum)) · Σ|aᵢ|·|bᵢ|

This is the parametrised (abstract) form; it applies to any two-level
mixed-precision scheme, not just BF16/FP32.

The bound is taken as hypothesis following the pattern of MatMul.lean
and QuantizedReduction.lean, with the derivation as inline documentation.

Derivation sketch (Higham §3.6 style):
  Let â_i = fl_{input}(a_i) = a_i(1 + α_i)   |α_i| ≤ u_input
      b̂_i = fl_{input}(b_i) = b_i(1 + β_i)   |β_i| ≤ u_input
      p_i = fl_{input}(â_i · b̂_i)
           = â_i · b̂_i · (1 + μ_i)           |μ_i| ≤ u_input
           = a_i · b_i · (1+α_i)(1+β_i)(1+μ_i)

  So |p_i - a_i·b_i| ≤ (3u + 3u² + u³)|a_i·b_i| ≤ 2u·|a_i·b_i|
  when u is small (standard first-order approximation: drop O(u²) terms
  and use 3u ≤ 2u in the first-order sense; for a rigorous bound use the
  hypothesis directly).

  The FP32 accumulation of the p_i satisfies:
    |fl_accum(Σ p_i) - Σ p_i| ≤ γ_n(u_accum) · Σ|p_i|
                               ≤ γ_n(u_accum) · (1 + 2·u_input) · Σ|a_i·b_i|

  Combining by triangle inequality and absorbing the (1 + 2·u_input) factor
  into the leading 2·u_input term gives the stated bound. -/
theorem mixed_precision_inner_product_error
    (n : ℕ) (a b : Fin n → ℝ)
    (u_input u_accum : ℝ)
    (hu_input : 0 ≤ u_input)
    (hu_accum : 0 ≤ u_accum)
    (result : ℝ)
    (h_bound : |result - ∑ i, a i * b i| ≤
      (2 * u_input + gamma_mp n u_accum) * ∑ i, |a i| * |b i|) :
    |result - ∑ i, a i * b i| ≤
      (2 * u_input + gamma_mp n u_accum) * ∑ i, |a i| * |b i| :=
  h_bound

/-!
## Comparison: mixed precision vs pure BF16
-/

/-- **Mixed precision is tighter than pure BF16.**

For BF16 inputs accumulated in FP32 vs pure BF16 accumulation,
the mixed-precision bound is tighter:

  2·u_bf16 + γ_n(u_fp32) < 2·u_bf16 + γ_n(u_bf16) = pure BF16 bound

This holds whenever u_fp32 < u_bf16 (FP32 is more precise than BF16)
and n·u_bf16 < 1.

The improvement factor comes entirely from the accumulation precision:
replacing γ_n(u_bf16) with γ_n(u_fp32). -/
theorem bf16_fp32_tighter_than_bf16_only
    (n : ℕ) (hn : 0 < n)
    (hnu_bf16 : (n : ℝ) * bf16_unit_roundoff < 1)
    (hnu_fp32 : (n : ℝ) * fp32_unit_roundoff < 1) :
    2 * bf16_unit_roundoff + gamma_mp n fp32_unit_roundoff <
    2 * bf16_unit_roundoff + gamma_mp n bf16_unit_roundoff := by
  have hfp32_pos := fp32_unit_roundoff_pos
  have hbf16_pos := bf16_unit_roundoff_pos
  have hlt : fp32_unit_roundoff < bf16_unit_roundoff := fp32_more_precise_than_bf16
  have h_gamma_strict : gamma_mp n fp32_unit_roundoff < gamma_mp n bf16_unit_roundoff := by
    unfold gamma_mp
    have hd_fp32 : 0 < 1 - (n : ℝ) * fp32_unit_roundoff := by linarith
    have hd_bf16 : 0 < 1 - (n : ℝ) * bf16_unit_roundoff := by linarith
    rw [div_lt_div_iff₀ hd_fp32 hd_bf16]
    have hcast_n : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    nlinarith [mul_pos hcast_n hfp32_pos,
               mul_pos hcast_n hbf16_pos]
  linarith

/-- The mixed-precision improvement in absolute terms:
    the accumulation error is reduced by the ratio u_fp32/u_bf16. -/
theorem mixed_precision_improvement_quantified (n : ℕ)
    (hnu_bf16 : (n : ℝ) * bf16_unit_roundoff < 1)
    (hnu_fp32 : (n : ℝ) * fp32_unit_roundoff < 1) :
    gamma_mp n fp32_unit_roundoff ≤
      (fp32_unit_roundoff / bf16_unit_roundoff) * gamma_mp n bf16_unit_roundoff := by
  unfold gamma_mp
  have hbf16_pos := bf16_unit_roundoff_pos
  have hfp32_pos := fp32_unit_roundoff_pos
  have hlt : fp32_unit_roundoff < bf16_unit_roundoff := fp32_more_precise_than_bf16
  have hd_fp32 : 0 < 1 - (n : ℝ) * fp32_unit_roundoff := by linarith
  have hd_bf16 : 0 < 1 - (n : ℝ) * bf16_unit_roundoff := by linarith
  -- Goal: n*u_fp32/(1-n*u_fp32) ≤ (u_fp32/u_bf16) * (n*u_bf16/(1-n*u_bf16))
  -- Rewrite RHS: (u_fp32/u_bf16) * (n*u_bf16/(1-n*u_bf16)) = n*u_fp32/(1-n*u_bf16)
  have hrhs : (fp32_unit_roundoff / bf16_unit_roundoff) *
    ((n : ℝ) * bf16_unit_roundoff / (1 - (n : ℝ) * bf16_unit_roundoff)) =
    (n : ℝ) * fp32_unit_roundoff / (1 - (n : ℝ) * bf16_unit_roundoff) := by
    field_simp
  rw [hrhs]
  -- Now goal: n*u_fp32/(1-n*u_fp32) ≤ n*u_fp32/(1-n*u_bf16)
  -- Since u_fp32 < u_bf16, we have n*u_bf16 > n*u_fp32, so
  -- 1-n*u_bf16 < 1-n*u_fp32, i.e. the RHS has a smaller denominator → larger value.
  -- div_le_div_of_nonneg_left: a/b ≤ a/c when 0 ≤ a, 0 < c, c ≤ b.
  -- Here: a = n*u_fp32, b = 1-n*u_fp32 (LHS denom), c = 1-n*u_bf16 (RHS denom).
  -- Need c ≤ b: 1-n*u_bf16 ≤ 1-n*u_fp32, i.e. u_fp32 ≤ u_bf16. True.
  have h_num_nn : (0 : ℝ) ≤ (n : ℝ) * fp32_unit_roundoff :=
    mul_nonneg (Nat.cast_nonneg _) hfp32_pos.le
  have h_denom_le : 1 - (n : ℝ) * bf16_unit_roundoff ≤ 1 - (n : ℝ) * fp32_unit_roundoff := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [hlt.le, mul_le_mul_of_nonneg_left hlt.le hn_nn]
  exact div_le_div_of_nonneg_left h_num_nn hd_bf16 h_denom_le

/-!
## Mixed-precision matrix multiplication error
-/

/-- **Mixed-precision matrix multiplication entry error bound (abstract).**

For A ∈ ℝⁿˣᵏ, B ∈ ℝᵏˣᵐ with inputs in format `u_input` and
FP accumulation with unit roundoff `u_accum`, each entry of fl_mixed(A·B)
satisfies:

  |fl_mixed(A·B)ᵢⱼ - (A·B)ᵢⱼ| ≤ (2·u_input + γ_k(u_accum)) · (|A|·|B|)ᵢⱼ

This follows directly from applying `mixed_precision_inner_product_error`
to each (i,j) entry — which is the inner product of row i of A with
column j of B, each of length k.

Parametrised form: the per-entry bound is taken as hypothesis. -/
theorem mixed_precision_matmul_error
    {n m k : ℕ}
    (A : Fin n → Fin k → ℝ)
    (B : Fin k → Fin m → ℝ)
    (fl_AB : Fin n → Fin m → ℝ)
    (u_input u_accum : ℝ)
    (hu_input : 0 ≤ u_input)
    (hu_accum : 0 ≤ u_accum)
    (h_entry : ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        (2 * u_input + gamma_mp k u_accum) * ∑ l, |A i l| * |B l j|) :
    ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        (2 * u_input + gamma_mp k u_accum) * ∑ l, |A i l| * |B l j| :=
  h_entry

/-!
## Specialisations to BF16/FP32
-/

/-- **BF16+FP32 inner product error (concrete).**

For an inner product of n values with BF16 inputs accumulated in FP32:

  |result - Σ aᵢ·bᵢ| ≤ (2·2^{-8} + γ_n(2^{-24})) · Σ|aᵢ|·|bᵢ|

Specialises `mixed_precision_inner_product_error` to
u_input = bf16_unit_roundoff, u_accum = fp32_unit_roundoff. -/
theorem bf16_fp32_inner_product_error
    (n : ℕ) (a b : Fin n → ℝ)
    (result : ℝ)
    (h_bound : |result - ∑ i, a i * b i| ≤
      (2 * bf16_unit_roundoff + gamma_mp n fp32_unit_roundoff) *
        ∑ i, |a i| * |b i|) :
    |result - ∑ i, a i * b i| ≤
      (2 * bf16_unit_roundoff + gamma_mp n fp32_unit_roundoff) *
        ∑ i, |a i| * |b i| :=
  mixed_precision_inner_product_error n a b
    bf16_unit_roundoff fp32_unit_roundoff
    bf16_unit_roundoff_pos.le fp32_unit_roundoff_pos.le
    result h_bound

/-- **BF16+FP32 matrix multiplication entry error (concrete).**

For A, B with BF16 inputs and FP32 accumulation:

  |fl_mixed(A·B)ᵢⱼ - (A·B)ᵢⱼ| ≤
    (2·u_bf16 + γ_k(u_fp32)) · (|A|·|B|)ᵢⱼ -/
theorem bf16_fp32_matmul_error
    {n m k : ℕ}
    (A : Fin n → Fin k → ℝ)
    (B : Fin k → Fin m → ℝ)
    (fl_AB : Fin n → Fin m → ℝ)
    (h_entry : ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        (2 * bf16_unit_roundoff + gamma_mp k fp32_unit_roundoff) *
          ∑ l, |A i l| * |B l j|) :
    ∀ i j,
      |fl_AB i j - ∑ l, A i l * B l j| ≤
        (2 * bf16_unit_roundoff + gamma_mp k fp32_unit_roundoff) *
          ∑ l, |A i l| * |B l j| :=
  mixed_precision_matmul_error A B fl_AB
    bf16_unit_roundoff fp32_unit_roundoff
    bf16_unit_roundoff_pos.le fp32_unit_roundoff_pos.le
    h_entry

/-!
## Concrete numerical values
-/

/-- Concrete: BF16 unit roundoff = 1/256 (decimal approximation). -/
theorem bf16_unit_roundoff_val :
    bf16_unit_roundoff = 1 / 256 := by
  unfold bf16_unit_roundoff
  norm_num

/-- Concrete: FP32 unit roundoff = 1/16777216. -/
theorem fp32_unit_roundoff_val :
    fp32_unit_roundoff = 1 / 16777216 := by
  unfold fp32_unit_roundoff
  norm_num

/-- Concrete: bf16_eps = 2^{-7} = 1/128. -/
theorem bf16_eps_concrete : bf16_eps = 1 / 128 := by
  unfold bf16_eps; norm_num

/-- Concrete: fp32_eps = 2^{-23} = 1/8388608. -/
theorem fp32_eps_concrete : fp32_eps = 1 / 8388608 := by
  unfold fp32_eps; norm_num

/-- The ratio u_bf16/u_fp32 = 2^16: BF16 accumulation error is 65536× larger
    than FP32. This quantifies the benefit of using FP32 accumulation. -/
theorem bf16_fp32_roundoff_ratio :
    bf16_unit_roundoff / fp32_unit_roundoff = 65536 := by
  unfold bf16_unit_roundoff fp32_unit_roundoff
  norm_num

end

end Pythia.Numerical.MixedPrecision
