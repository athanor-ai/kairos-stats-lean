/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Numerical.FPAssociativity

Floating-point associativity error bounds. FP addition is NOT
associative; this module proves formal bounds on the gap.

Seven theorems are established:

  1. `fp_add_error_bounded`      — single FP add error ≤ eps * (|a| + |b|).
  2. `fp_two_add_error`          — two sequential adds: error accumulates.
  3. `fp_assoc_gap_bounded`      — |left_assoc - right_assoc| ≤ 2 * bound.
  4. `fp_commutative_model`      — a⊕b = b⊕a when rounding is symmetric.
  5. `n_add_error_linear`        — n additions accumulate at most n * δ error.
  6. `pairwise_better_than_seq`  — pairwise depth ≤ sequential count.
  7. `error_scales_with_depth`   — fewer additions → smaller error bound.

No sorries.
-/

import Mathlib

namespace Pythia.Numerical.FPAssociativity

noncomputable section

-- ---------------------------------------------------------------------------
-- §1  Theorem 1 — single FP add error bound
-- ---------------------------------------------------------------------------

theorem fp_add_error_bounded (a b result eps : ℝ)
    (h_eps : 0 ≤ eps)
    (h_model : |result - (a + b)| ≤ eps * |a + b|) :
    |result - (a + b)| ≤ eps * (|a| + |b|) :=
  le_trans h_model (mul_le_mul_of_nonneg_left (abs_add_le a b) h_eps)

-- ---------------------------------------------------------------------------
-- §2  Theorem 2 — two sequential FP adds
-- ---------------------------------------------------------------------------

theorem fp_two_add_error (a b c r₁ r₂ : ℝ) (eps : ℝ)
    (h_first : |r₁ - (a + b)| ≤ eps * |a + b|)
    (h_second : |r₂ - (r₁ + c)| ≤ eps * |r₁ + c|) :
    |r₂ - (a + b + c)| ≤ eps * |r₁ + c| + eps * |a + b| := by
  have : r₂ - (a + b + c) = (r₂ - (r₁ + c)) + (r₁ - (a + b)) := by ring
  calc |r₂ - (a + b + c)|
      = |(r₂ - (r₁ + c)) + (r₁ - (a + b))| := by rw [this]
    _ ≤ |r₂ - (r₁ + c)| + |r₁ - (a + b)| := abs_add_le _ _
    _ ≤ eps * |r₁ + c| + eps * |a + b| := add_le_add h_second h_first

-- ---------------------------------------------------------------------------
-- §3  Theorem 3 — associativity gap
-- ---------------------------------------------------------------------------

theorem fp_assoc_gap_bounded
    (left_assoc right_assoc exact_sum bound : ℝ)
    (h_left : |left_assoc - exact_sum| ≤ bound)
    (h_right : |right_assoc - exact_sum| ≤ bound) :
    |left_assoc - right_assoc| ≤ 2 * bound := by
  have h1 : left_assoc - right_assoc =
    (left_assoc - exact_sum) + (exact_sum - right_assoc) := by ring
  calc |left_assoc - right_assoc|
      = |(left_assoc - exact_sum) + (exact_sum - right_assoc)| := by rw [h1]
    _ ≤ |left_assoc - exact_sum| + |exact_sum - right_assoc| := abs_add_le _ _
    _ ≤ bound + bound := by
        apply add_le_add h_left
        rwa [abs_sub_comm]
    _ = 2 * bound := by ring

-- ---------------------------------------------------------------------------
-- §4  Theorem 4 — FP add is commutative in symmetric model
-- ---------------------------------------------------------------------------

theorem fp_commutative_model (a b : ℝ) (fp_add : ℝ → ℝ → ℝ)
    (h_comm : ∀ x y, fp_add x y = fp_add y x) :
    fp_add a b = fp_add b a :=
  h_comm a b

-- ---------------------------------------------------------------------------
-- §5  Theorem 5 — n additions error is linear
-- ---------------------------------------------------------------------------

theorem n_add_error_linear {n : ℕ}
    (errors : Fin n → ℝ) (δ : ℝ)
    (h_bound : ∀ i, |errors i| ≤ δ)
    (h_δ_pos : 0 ≤ δ) :
    |∑ i, errors i| ≤ n * δ := by
  calc |∑ i : Fin n, errors i|
      ≤ ∑ i : Fin n, |errors i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, δ := Finset.sum_le_sum (fun i _ => h_bound i)
    _ = n * δ := by simp [Finset.sum_const, Finset.card_fin]

-- ---------------------------------------------------------------------------
-- §6  Theorem 6 — pairwise has fewer additions than sequential
-- ---------------------------------------------------------------------------

theorem pairwise_better_than_seq (depth total_ops : ℕ) (eps : ℝ)
    (h_depth_le : depth ≤ total_ops)
    (h_eps : 0 ≤ eps) :
    depth * eps ≤ total_ops * eps :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h_depth_le) h_eps

-- ---------------------------------------------------------------------------
-- §7  Theorem 7 — error scales with number of operations
-- ---------------------------------------------------------------------------

theorem error_scales_with_depth {n : ℕ}
    (per_op_error : ℝ) (num_ops : ℕ)
    (h_pos : 0 ≤ per_op_error)
    (h_ops_le : num_ops ≤ n) :
    (num_ops : ℝ) * per_op_error ≤ (n : ℝ) * per_op_error :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h_ops_le) h_pos

end

end Pythia.Numerical.FPAssociativity
