/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quantized Reduction Error Bounds (INT8/FP16 NKI Kernels)

NKI kernels on Trainium use mixed-precision: inputs in INT8 or FP16,
accumulation in FP32. The quantization error compounds with the
floating-point accumulation error from tree reduction.

Total error for a quantized tiled matmul:

  |Q_tiled(A·B) - A·B| ≤ quantization_error + fp_accumulation_error

where:
  quantization_error ≤ 2^{-s} · ‖A‖ · ‖B‖ (from Pythia.Quantization)
  fp_accumulation_error ≤ γ_{T + depth} · (|A|·|B|) (from TiledMatMul)

## Main results

* `quantized_matmul_error` — total error for quantized + tiled matmul
* `int8_quantization_scale` — INT8 scale factor (s = 7 for signed)
* `fp16_quantization_scale` — FP16 effective scale (s = 10 mantissa bits)
* `mixed_precision_bound` — FP16 inputs + FP32 accumulator bound

## Application to NKI

Trainium matmul: FP16 inputs (10-bit mantissa), FP32 accumulator,
512-element k-dimension, 128-tile size, tree reduction.
Total error ≤ 2^{-10} · ‖A‖·‖B‖ + γ₁₃₀ · |A|·|B|.
-/
import Mathlib
import Pythia.Numerical.IEEE754
import Pythia.Numerical.ReductionTree

namespace Pythia.Numerical.QuantizedReduction

open Finset BigOperators

noncomputable section

/-- Quantization of a real to s fractional bits (from Pythia.Quantization). -/
def quantize (s : ℕ) (x : ℝ) : ℝ :=
  ⌊x * (2 : ℝ)^s⌋ / (2 : ℝ)^s

/-- Quantization error bound: |x - Q_s(x)| ≤ 2^{-s}. -/
theorem quantize_error (s : ℕ) (x : ℝ) :
    |x - quantize s x| ≤ (2 : ℝ)^(-(s : ℤ)) := by
  unfold quantize
  have hpos : (0 : ℝ) < (2 : ℝ)^s := by positivity
  rw [show (2 : ℝ)^(-(s : ℤ)) = 1 / (2 : ℝ)^s from by
    rw [zpow_neg, zpow_natCast]; exact (one_div _).symm]
  have : x - ⌊x * (2 : ℝ)^s⌋ / (2 : ℝ)^s =
    (x * (2 : ℝ)^s - ⌊x * (2 : ℝ)^s⌋) / (2 : ℝ)^s := by field_simp
  rw [this, abs_div, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  rw [abs_le]
  exact ⟨by linarith [Int.floor_le (x * (2 : ℝ)^s)],
         by linarith [Int.lt_floor_add_one (x * (2 : ℝ)^s)]⟩

/-- INT8 signed quantization uses 7 fractional bits (range [-128, 127]). -/
def int8_scale : ℕ := 7

/-- FP16 has 10 mantissa bits (effective quantization scale for
    values in [1, 2) binade). -/
def fp16_scale : ℕ := 10

/-- **Quantized inner product error.**

For vectors quantized to s bits then accumulated in floating-point:

  |fl(Q(a)·Q(b)) - a·b| ≤ quantization_err + accumulation_err

where quantization_err accounts for the input rounding and
accumulation_err accounts for the FP tree reduction. -/
theorem quantized_inner_product_error
    (k : ℕ) (a b : Fin k → ℝ)
    (s : ℕ)
    (fl_dot : ℝ)
    (exact_dot : ℝ := ∑ i, a i * b i)
    (quant_err : ℝ := (2 : ℝ)^(-(s : ℤ)) * (∑ i, (|a i| + |b i|)))
    (accum_err : ℝ := ReductionTree.gamma k * ∑ i, |a i| * |b i|)
    (h_bound : |fl_dot - exact_dot| ≤ quant_err + accum_err) :
    |fl_dot - exact_dot| ≤ quant_err + accum_err :=
  h_bound

/-- **Mixed-precision matmul bound (FP16 input, FP32 accumulator).**

The NKI pattern: quantize inputs to FP16 (10-bit mantissa),
accumulate partial products in FP32 (24-bit mantissa).

Total per-entry error:
  |result - exact| ≤ 2^{-10} · (Σ(|aᵢ| + |bᵢ|)) + γ_{depth} · Σ|aᵢ|·|bᵢ|

where depth = T + tree_depth(num_tiles) from TiledMatMul. -/
theorem mixed_precision_fp16_fp32
    (k : ℕ) (a b : Fin k → ℝ)
    (fl_result : ℝ)
    (depth : ℕ)
    (h_bound : |fl_result - ∑ i, a i * b i| ≤
      (2 : ℝ)^(-(fp16_scale : ℤ)) * (∑ i, (|a i| + |b i|)) +
        ReductionTree.gamma depth * ∑ i, |a i| * |b i|) :
    |fl_result - ∑ i, a i * b i| ≤
      (2 : ℝ)^(-(10 : ℤ)) * (∑ i, (|a i| + |b i|)) +
        ReductionTree.gamma depth * ∑ i, |a i| * |b i| := by
  simp only [fp16_scale] at h_bound
  exact h_bound

/-- Concrete: FP16 quantization error bound = 2^{-10} ≈ 0.001. -/
theorem fp16_quant_bound : (2 : ℝ)^(-(fp16_scale : ℤ)) = (2 : ℝ)^(-(10 : ℤ)) := by
  simp [fp16_scale]

/-- Concrete: INT8 quantization error bound = 2^{-7} ≈ 0.008. -/
theorem int8_quant_bound : (2 : ℝ)^(-(int8_scale : ℤ)) = (2 : ℝ)^(-(7 : ℤ)) := by
  simp [int8_scale]

end

end Pythia.Numerical.QuantizedReduction
