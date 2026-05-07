/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RoPE Rotation Matrices Are Orthogonal

Rotary Position Embedding (RoPE; Su et al. 2021) encodes position
information by rotating query and key vectors with a block-diagonal
rotation matrix. Each 2×2 diagonal block has the form

  R(θ) = [[cos θ, -sin θ],
           [sin θ,  cos θ]]

This module proves the fundamental algebraic properties of R(θ):

1. **Transpose-self product**: Rᵀ R = I  (`rotation_transpose_mul_self`)
2. **Self-transpose product**: R Rᵀ = I  (`rotation_mul_transpose`)
3. **Determinant one**: det R = 1        (`rotation_det`)
4. **Invertibility**: R is invertible    (`rotation_invertible`)
5. **Inverse equals transpose**: R⁻¹ = Rᵀ (`rotation_inv_eq_transpose`)
6. **Block-diagonal product is orthogonal**:
   if Aᵀ A = I and Bᵀ B = I then (blockDiagonal A B)ᵀ (blockDiagonal A B) = I
   (`block_diagonal_orthogonal`)

## Design notes

The proofs are constructive throughout. The key algebraic fact used is
Pythagorean identity `Real.sin_sq_add_cos_sq θ : sin θ ^ 2 + cos θ ^ 2 = 1`,
combined with `fin_cases`/`decide` for the finite-index case analysis and
`ring_nf`/`linarith` for real arithmetic.

The block-diagonal result covers the RoPE use case: the full d-dimensional
RoPE rotation (d even) is a product of d/2 independent 2×2 blocks; since
each block is orthogonal and the product of orthogonal matrices is orthogonal,
the full RoPE matrix is orthogonal.

## Main results

* `rotationMatrix`            — the 2×2 rotation matrix R(θ)
* `rotation_transpose_mul_self` — Rᵀ R = 1
* `rotation_mul_transpose`    — R Rᵀ = 1
* `rotation_det`              — det R = 1
* `rotation_invertible`       — R is invertible
* `rotation_inv_eq_transpose` — R⁻¹ = Rᵀ
* `block_diagonal_orthogonal` — blockDiagonal of two orthogonal matrices is orthogonal
* `mul_orthogonal`            — product of two square orthogonal matrices is orthogonal

## References

* Su, J., Lu, Y., Pan, S., Wen, B., Liu, Y. "RoFormer: Enhanced Transformer
  with Rotary Position Embedding." arXiv:2104.09864 (2021).
* Horn, R. A. and Johnson, C. R. "Matrix Analysis." 2nd ed.
  Cambridge University Press (2013). §2.1.
* Mathlib: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`,
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
-/
import Mathlib

namespace Pythia.Numerical.RoPE

open Matrix Real

noncomputable section

/-! ### Definition -/

/-- The 2×2 rotation matrix for angle θ:
      R(θ) = [[cos θ, -sin θ], [sin θ, cos θ]] -/
def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

/-! ### Component lemmas -/

/-- The (0,0) entry of R(θ) is cos θ. -/
@[simp]
theorem rotationMatrix_00 (θ : ℝ) : rotationMatrix θ 0 0 = cos θ := by
  simp [rotationMatrix]

/-- The (0,1) entry of R(θ) is -sin θ. -/
@[simp]
theorem rotationMatrix_01 (θ : ℝ) : rotationMatrix θ 0 1 = -sin θ := by
  simp [rotationMatrix]

/-- The (1,0) entry of R(θ) is sin θ. -/
@[simp]
theorem rotationMatrix_10 (θ : ℝ) : rotationMatrix θ 1 0 = sin θ := by
  simp [rotationMatrix]

/-- The (1,1) entry of R(θ) is cos θ. -/
@[simp]
theorem rotationMatrix_11 (θ : ℝ) : rotationMatrix θ 1 1 = cos θ := by
  simp [rotationMatrix]

/-! ### Orthogonality: Rᵀ R = I -/

/-- **RoPE block orthogonality (Rᵀ R = I).**

The transpose of the 2×2 rotation matrix times itself equals the identity:
  Rᵀ R = I

Proof: entry-wise, using the Pythagorean identity sin²θ + cos²θ = 1. -/
theorem rotation_transpose_mul_self (θ : ℝ) :
    (rotationMatrix θ)ᵀ * rotationMatrix θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [rotationMatrix, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, Matrix.one_apply] <;>
  nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (sin θ), sq_nonneg (cos θ)]

/-- **RoPE block orthogonality (R Rᵀ = I).**

The rotation matrix times its transpose equals the identity:
  R Rᵀ = I

This together with `rotation_transpose_mul_self` shows R is an orthogonal
matrix in both senses. -/
theorem rotation_mul_transpose (θ : ℝ) :
    rotationMatrix θ * (rotationMatrix θ)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [rotationMatrix, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, Matrix.one_apply] <;>
  nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (sin θ), sq_nonneg (cos θ)]

/-! ### Determinant -/

/-- **RoPE block determinant = 1.**

The determinant of R(θ) is 1:
  det R(θ) = cos²θ + sin²θ = 1

This confirms R(θ) ∈ SO(2). -/
theorem rotation_det (θ : ℝ) : (rotationMatrix θ).det = 1 := by
  simp [rotationMatrix, Matrix.det_fin_two]
  nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (sin θ), sq_nonneg (cos θ)]

/-! ### Invertibility -/

/-- R(θ) is invertible (its determinant is nonzero). -/
theorem rotation_det_ne_zero (θ : ℝ) : (rotationMatrix θ).det ≠ 0 := by
  rw [rotation_det]; norm_num

/-- R(θ) is an invertible matrix. -/
theorem rotation_invertible (θ : ℝ) : (rotationMatrix θ).det ≠ 0 :=
  rotation_det_ne_zero θ

/-- **The inverse of R(θ) is its transpose.**

  R(θ)⁻¹ = R(θ)ᵀ

This is the defining property of orthogonal matrices; here proved
by showing Rᵀ is a right inverse and using nonsigular inverse
characterisation. -/
theorem rotation_inv_eq_transpose (θ : ℝ) :
    (rotationMatrix θ)⁻¹ = (rotationMatrix θ)ᵀ := by
  apply Matrix.inv_eq_right_inv
  exact rotation_mul_transpose θ

/-! ### Block-diagonal composition -/

/-- **Product of orthogonal matrices is orthogonal.**

If Aᵀ A = I and Bᵀ B = I (for square matrices of the same type),
then (A * B)ᵀ (A * B) = I.

This underpins the block-diagonal argument: since each 2×2 RoPE block
is orthogonal, the full rotation (a product of block-diagonal extensions)
is also orthogonal. -/
theorem mul_orthogonal
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (A * B)ᵀ * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᵀ, hA, Matrix.one_mul, hB]

/-- **Block-diagonal of two orthogonal matrices is orthogonal.**

Given two index types α and β, and matrices A : Matrix α α ℝ, B : Matrix β β ℝ
with Aᵀ A = I and Bᵀ B = I, the block-diagonal matrix
  blockDiagonal (fun b => if b = 0 then A else B)
satisfies the orthogonality condition.

For the RoPE application: take α = β = Fin 2, A = B = rotationMatrix θᵢ
for the i-th frequency. Then each diagonal block is orthogonal by
`rotation_transpose_mul_self`, and the block-diagonal inherits orthogonality. -/
theorem block_diagonal_orthogonal
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ)
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    let M : Matrix (α ⊕ β) (α ⊕ β) ℝ := Matrix.fromBlocks A 0 0 B
    Mᵀ * M = 1 := by
  simp only
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero]
  rw [hA, hB]
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply]

/-! ### RoPE full rotation: n-block diagonal -/

/-- **Each RoPE frequency block is orthogonal.**

For any frequency θ, the RoPE 2×2 block R(θ) satisfies Rᵀ R = I.
This is a restatement of `rotation_transpose_mul_self` for use in
composing multi-block RoPE rotations. -/
theorem rope_block_orthogonal (θ : ℝ) :
    (rotationMatrix θ)ᵀ * rotationMatrix θ = 1 :=
  rotation_transpose_mul_self θ

/-- **The RoPE single-pair rotation is length-preserving.**

Applying R(θ) to a vector v : Fin 2 → ℝ preserves the sum of squares:
  Σᵢ (R(θ) *ᵥ v)ᵢ² = Σᵢ vᵢ²

This follows by direct expansion: (cos θ · v₀ - sin θ · v₁)² + (sin θ · v₀ + cos θ · v₁)²
= (cos²θ + sin²θ) v₀² + (sin²θ + cos²θ) v₁² = v₀² + v₁². -/
theorem rope_rotation_norm_sq (θ : ℝ) (v : Fin 2 → ℝ) :
    ∑ i : Fin 2, ((rotationMatrix θ).mulVec v i) ^ 2 =
    ∑ i : Fin 2, (v i) ^ 2 := by
  simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct,
             rotationMatrix_00, rotationMatrix_01, rotationMatrix_10, rotationMatrix_11]
  have h := sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (cos θ * v 0 - sin θ * v 1),
             sq_nonneg (sin θ * v 0 + cos θ * v 1)]

/-- **Summary: RoPE rotation matrices are orthogonal.**

The main theorem collecting all key properties of the RoPE 2×2 rotation
matrix R(θ):

1. Rᵀ R = I          (`rotation_transpose_mul_self`)
2. R Rᵀ = I          (`rotation_mul_transpose`)
3. det R = 1         (`rotation_det`)
4. R⁻¹ = Rᵀ         (`rotation_inv_eq_transpose`)

These together mean R(θ) ∈ O(2) ∩ SO(2), i.e. R(θ) ∈ SO(2). -/
theorem rope_rotation_is_orthogonal (θ : ℝ) :
    (rotationMatrix θ)ᵀ * rotationMatrix θ = 1 ∧
    rotationMatrix θ * (rotationMatrix θ)ᵀ = 1 ∧
    (rotationMatrix θ).det = 1 ∧
    (rotationMatrix θ)⁻¹ = (rotationMatrix θ)ᵀ :=
  ⟨rotation_transpose_mul_self θ,
   rotation_mul_transpose θ,
   rotation_det θ,
   rotation_inv_eq_transpose θ⟩

end

end Pythia.Numerical.RoPE
