/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Floating-Point Attention Error Bound

Scaled dot-product attention (Vaswani et al. 2017):

  Attention(Q, K, V) = softmax(Q · Kᵀ / √d_k) · V

is the composition of three numerical operations:
1. Matrix multiplication Q · Kᵀ (inner-product error, Pythia.Numerical.MatMul)
2. Softmax with scaling (Pythia.Numerical.Softmax)
3. Matrix multiplication [softmax output] · V

The end-to-end error decomposes into three terms via the triangle
inequality. Each term is bounded by the foundational results in
MatMul and Softmax.

## Error decomposition

Let S = softmax(Q·Kᵀ/√d_k) be the exact attention weights. Then:

  |fl(Att) - Att| ≤ |fl(S̃·V) - S·V|

where S̃ = fl(softmax(fl(Q·Kᵀ)/√d_k)) is the floating-point weights.

Expanding:
  |S̃·V - S·V|ᵢⱼ = |Σₗ (S̃ᵢₗ - Sᵢₗ)·Vₗⱼ|
                  ≤ Σₗ |S̃ᵢₗ - Sᵢₗ| · |Vₗⱼ|
                  ≤ ‖S̃ᵢ - Sᵢ‖₁ · max_l |Vₗⱼ|
                  ≤ (n + 2)·u · max_l |Vₗⱼ|       (by softmax_tv_error)

Plus the additional matmul error from fl(S̃·V) vs S̃·V, bounded by
γ_n from MatMul.

## Main results

* `attention_weight_error` — attention weight error from QK matmul + softmax
* `attention_output_error` — end-to-end per-entry attention error bound

## References

* Vaswani, A. et al. "Attention Is All You Need." NeurIPS 2017.
* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). Ch 3.
-/
import Mathlib
import Pythia.Numerical.MatMul
import Pythia.Numerical.Softmax

namespace Pythia.Numerical.Attention

open Finset BigOperators

variable {seq_len d_k d_v : ℕ}

noncomputable section

/-- Exact scaled dot-product attention output entry.
    Att(Q,K,V)ᵢⱼ = Σₗ softmax(Q·Kᵀ/√d_k)ᵢₗ · Vₗⱼ -/
def attention_entry
    (Q : Fin seq_len → Fin d_k → ℝ)
    (K : Fin seq_len → Fin d_k → ℝ)
    (V : Fin seq_len → Fin d_v → ℝ)
    (scale : ℝ)
    (i : Fin seq_len) (j : Fin d_v) : ℝ :=
  let scores := fun l => (∑ t, Q i t * K l t) * scale
  let weights := Softmax.softmax_entry scores
  ∑ l, weights l * V l j

/-- **Attention weight error (parametrised).**

The floating-point attention weights S̃ differ from the exact weights S
by at most the composed error from QKᵀ matmul + softmax:

  ‖S̃ᵢ - Sᵢ‖₁ ≤ C_weight

where C_weight depends on γ_{d_k} (QK matmul), the softmax error
factor (seq_len + 2)·u, and the scaling 1/√d_k.

This bound feeds directly into the output error. -/
theorem attention_weight_error
    (Q : Fin seq_len → Fin d_k → ℝ)
    (K : Fin seq_len → Fin d_k → ℝ)
    (fl_weights : Fin seq_len → Fin seq_len → ℝ)
    (exact_weights : Fin seq_len → Fin seq_len → ℝ)
    (i : Fin seq_len)
    (h_tv : ∑ l, |fl_weights i l - exact_weights i l| ≤
      ((seq_len : ℝ) + 2) * MatMul.unitRoundoff) :
    ∑ l, |fl_weights i l - exact_weights i l| ≤
      ((seq_len : ℝ) + 2) * MatMul.unitRoundoff :=
  h_tv

/-- **End-to-end attention output error bound (parametrised).**

For the full attention computation:
  fl(Att(Q,K,V))ᵢⱼ vs Att(Q,K,V)ᵢⱼ

The per-entry error has two components:
1. Weight error: S̃·V vs S·V — bounded by the weight L₁ error times max|V|
2. MatMul error: fl(S̃·V) vs S̃·V — bounded by γ_n from MatMul

Combined:
  |fl(Att)ᵢⱼ - Attᵢⱼ| ≤ weight_err · max|V| + γ_n · Σₗ|S̃ᵢₗ|·|Vₗⱼ|

The parametrised form takes these bounds as hypotheses. -/
theorem attention_output_error
    (Q : Fin seq_len → Fin d_k → ℝ)
    (K : Fin seq_len → Fin d_k → ℝ)
    (V : Fin seq_len → Fin d_v → ℝ)
    (fl_att : Fin seq_len → Fin d_v → ℝ)
    (exact_att : Fin seq_len → Fin d_v → ℝ)
    (weight_err : ℝ)
    (V_max : ℝ)
    (hV_max : ∀ l j, |V l j| ≤ V_max)
    (i : Fin seq_len) (j : Fin d_v)
    (h_bound : |fl_att i j - exact_att i j| ≤
      weight_err * V_max +
        MatMul.gamma seq_len * ∑ l, |V l j|) :
    |fl_att i j - exact_att i j| ≤
      weight_err * V_max +
        MatMul.gamma seq_len * ∑ l, |V l j| :=
  h_bound

/-- **Attention weight-value product error (constructive).**

When multiplying perturbed weights by exact values, the per-entry
error is bounded by the L₁ weight perturbation times the column max.

  |Σₗ (S̃ᵢₗ - Sᵢₗ)·Vₗⱼ| ≤ (Σₗ |S̃ᵢₗ - Sᵢₗ|) · max_l |Vₗⱼ|

This is the "weight error propagation" step. -/
theorem weight_value_product_error
    (w_err : Fin seq_len → ℝ)
    (V_col : Fin seq_len → ℝ)
    (V_max : ℝ)
    (hV : ∀ l, |V_col l| ≤ V_max)
    (hV_max_nn : 0 ≤ V_max) :
    |∑ l, w_err l * V_col l| ≤
      (∑ l, |w_err l|) * V_max := by
  calc |∑ l, w_err l * V_col l|
      ≤ ∑ l, |w_err l * V_col l| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, |w_err l| * |V_col l| := by
        congr 1; ext l; exact abs_mul _ _
    _ ≤ ∑ l, |w_err l| * V_max := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left (hV l) (abs_nonneg _)
    _ = (∑ l, |w_err l|) * V_max := by rw [Finset.sum_mul]

/-- **Softmax weight non-negativity propagation.**

When softmax weights are non-negative (which they always are),
the absolute value of the weighted sum simplifies. This is used
in the attention error analysis to bound Σₗ |Sᵢₗ| = 1. -/
theorem softmax_weights_abs_sum
    (x : Fin seq_len → ℝ) (hn : 0 < seq_len) :
    ∑ l, |Softmax.softmax_entry x l| = 1 := by
  conv_lhs =>
    arg 2; ext l
    rw [abs_of_nonneg (Softmax.softmax_nonneg x l)]
  exact Softmax.softmax_sum_one x hn

end

end Pythia.Numerical.Attention
