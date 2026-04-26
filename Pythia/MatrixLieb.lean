/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lieb's Matrix Concavity Theorem

Lieb 1973 (Adv. Math. 11(3):267–288): For fixed Hermitian matrix `A` and `0 ≤ s ≤ 1`,
the map `(X, Y) ↦ tr exp(A + log X + s · log Y)` is jointly concave on positive-definite
matrices.

This is the foundational dependency for the Tropp (2012) matrix Bernstein inequality chain:
  Lieb → Klein matrix inequality → matrix MGF bound → Tropp matrix Bernstein.

## Implementation strategy

We build the required infrastructure on top of Mathlib's spectral theorem for Hermitian
matrices (`Matrix.IsHermitian.spectral_theorem`), which gives us the eigendecomposition
`A = U diag(λ) U*`. The **Hermitian functional calculus** applies a real-valued function
`f : ℝ → ℝ` entrywise to eigenvalues: `f(A) := U diag(f(λ)) U*`.

### What is proved

* `hermFuncCalc_id` — the identity function recovers the original matrix
* `hermFuncCalc_isHermitian` — the functional calculus preserves Hermitianness
* `traceConj_eq_trace` — trace invariance under unitary conjugation
* `trace_hermFuncCalc_eq_sum` — `tr(f(A)) = ∑ᵢ f(λᵢ)`
* `matExp_posDef` — matrix exponential of Hermitian is positive definite
* `matExp_isHermitian`, `matLog_isHermitian` — exp/log preserve Hermitianness
* `trace_matExp_eq_sum` — `tr(exp(A)) = ∑ᵢ exp(λᵢ)`
* `IsHermitian_add`, `IsHermitian_smul` — closure of Hermitian matrices under
  addition and real-scalar multiplication

### Mathlib v4.28 gaps (explicit named sorries)

* `matExp_matLog` — functoriality of spectral calculus (`exp ∘ log = id` on PD matrices).
  Requires showing that `hermFuncCalc` composed with itself uses the same eigenbasis,
  which needs a uniqueness/compatibility result for spectral decompositions not in Mathlib.
* `matLog_matExp` — same functoriality in the reverse direction.
* `lieb_concavity` — the core Lieb concavity inequality. Requires either Epstein's
  interpolation theorem or the Peierls–Bogoliubov inequality, neither in Mathlib v4.28.
* `lieb_concavity_s_eq_zero` — specialization of the above to `s = 0`.
* `golden_thompson` — the Golden–Thompson trace inequality `tr(exp(A+B)) ≤ tr(exp(A)exp(B))`.

## References

* E. H. Lieb, "Convex trace functions and the Wigner–Yanase–Dyson conjecture",
  Advances in Mathematics 11 (1973), 267–288.
* J. A. Tropp, "User-friendly tail bounds for sums of random matrices",
  Foundations of Computational Mathematics 12 (2012), 389–434.
-/

import Mathlib

open scoped Matrix ComplexOrder

noncomputable section

namespace MatrixLieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Section 1: Hermitian Functional Calculus

Given a Hermitian matrix `A` with spectral decomposition `A = U diag(λ) U*`,
define `f(A) := U diag(f(λ₁), …, f(λₙ)) U*` for any `f : ℝ → ℝ`. -/

/-- Apply a real-valued function to a Hermitian matrix via the spectral theorem.
    For `A = U diag(λ) U*`, defines `hermFuncCalc f A := U diag(f(λ)) U*`. -/
def hermFuncCalc {A : Matrix n n ℂ} (f : ℝ → ℝ) (hA : A.IsHermitian) : Matrix n n ℂ :=
  ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) hA.eigenvectorUnitary)
    (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)))

/-- The functional calculus of the identity function recovers the original matrix. -/
theorem hermFuncCalc_id {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermFuncCalc id hA = A := by
  unfold hermFuncCalc
  simp only [id, Function.comp]
  exact (hA.spectral_theorem).symm

/-- The functional calculus preserves Hermitianness. -/
theorem hermFuncCalc_isHermitian {A : Matrix n n ℂ} (f : ℝ → ℝ) (hA : A.IsHermitian) :
    (hermFuncCalc f hA).IsHermitian := by
  unfold hermFuncCalc; simp +decide [Matrix.IsHermitian]
  ext i j; simp +decide [Matrix.mul_apply, Matrix.diagonal]; ring

/-- Trace is invariant under unitary conjugation: `tr(U X U*) = tr(X)`. -/
theorem traceConj_eq_trace (U : ↥(Matrix.unitaryGroup n ℂ)) (X : Matrix n n ℂ) :
    ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U X).trace = X.trace := by
  convert Matrix.trace_mul_comm _ _ using 2
  all_goals try infer_instance
  simp +decide [← mul_assoc, U.2.2]

/-- The trace of `f(A)` equals the sum of `f` applied to eigenvalues.
    `tr(f(A)) = ∑ i, f(λᵢ)` -/
theorem trace_hermFuncCalc_eq_sum {A : Matrix n n ℂ} (f : ℝ → ℝ) (hA : A.IsHermitian) :
    (hermFuncCalc f hA).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  convert traceConj_eq_trace _ _ using 1
  simp +decide [Matrix.trace]

/-! ## Section 2: Matrix Exponential and Logarithm for Hermitian Matrices

We define `matExp` and `matLog` through the functional calculus rather than
via the power-series definition. For Hermitian matrices these coincide. -/

/-- Matrix exponential of a Hermitian matrix, defined via spectral decomposition.
    `matExp A := U diag(exp(λ₁), …, exp(λₙ)) U*` -/
def matExp {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  hermFuncCalc Real.exp hA

/-- Matrix logarithm of a positive-definite matrix, defined via spectral decomposition.
    `matLog A := U diag(log(λ₁), …, log(λₙ)) U*` -/
def matLog {A : Matrix n n ℂ} (hA : A.PosDef) : Matrix n n ℂ :=
  hermFuncCalc Real.log hA.isHermitian

/-- Matrix exponential of a Hermitian matrix is positive definite. -/
theorem matExp_posDef {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (matExp hA).PosDef := by
  refine ⟨?_, ?_⟩
  · exact hermFuncCalc_isHermitian _ _
  · intro x hx_nonzero
    have h_pos_def : 0 < ∑ i, ∑ j,
        star (x i) * (hermFuncCalc Real.exp hA) i j * x j := by
      have h_pos_def : 0 < ∑ i, ∑ j,
          star (x i) * (hA.eigenvectorUnitary * Matrix.diagonal
            (fun i => (Real.exp (hA.eigenvalues i) : ℂ)) *
            hA.eigenvectorUnitary⁻¹) i j * x j := by
        have h_pos_def : 0 < ∑ i, ∑ j,
            star ((hA.eigenvectorUnitary⁻¹.val.mulVec x) i) *
            (Matrix.diagonal (fun i => (Real.exp (hA.eigenvalues i) : ℂ))) i j *
            (hA.eigenvectorUnitary⁻¹.val.mulVec x) j := by
          have h_pos_def : 0 < ∑ i,
              (Real.exp (hA.eigenvalues i)) *
              ‖(hA.eigenvectorUnitary⁻¹.val.mulVec x) i‖ ^ 2 := by
            have h_pos_def : ∃ i,
                ‖(hA.eigenvectorUnitary⁻¹.val.mulVec x) i‖ ^ 2 > 0 := by
              contrapose! hx_nonzero
              have h_pos_def : hA.eigenvectorUnitary⁻¹.val.mulVec x = 0 := by
                exact funext fun i => norm_eq_zero.mp
                  (sq_eq_zero_iff.mp (le_antisymm (hx_nonzero i) (sq_nonneg _)))
              apply_fun (fun y => (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ y) at h_pos_def
              simp_all +decide [Matrix.mulVec_mulVec]
            exact lt_of_lt_of_le
              (mul_pos (Real.exp_pos _) h_pos_def.choose_spec)
              (Finset.single_le_sum
                (fun i _ => mul_nonneg (Real.exp_nonneg (hA.eigenvalues i))
                  (sq_nonneg (‖(hA.eigenvectorUnitary⁻¹.val.mulVec x) i‖)))
                (Finset.mem_univ _))
          simp_all +decide [Matrix.diagonal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          convert h_pos_def using 2; norm_num [Complex.ext_iff, sq]; ring
          norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im,
            mul_assoc, mul_comm, mul_left_comm, sq]
          norm_num [Complex.mul_conj, Complex.normSq_eq_norm_sq,
            Complex.exp_re, Complex.exp_im]
          norm_cast; norm_num [← sq]
        convert h_pos_def using 1
        simp +decide [Matrix.mul_assoc, Matrix.mulVec, dotProduct,
          mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul]
        simp +decide [Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm,
          Finset.mul_sum _ _ _, Finset.sum_mul]
        simp +decide only [← Finset.sum_product']
        apply Finset.sum_bij (fun x _ => (x.2.2.2, x.2.2.1, x.2.1, x.1))
        · grind +revert
        · grind
        · simp +decide
        · simp +decide [Matrix.diagonal]; grind
      convert h_pos_def using 1
    convert h_pos_def using 1
    simp +decide [Finsupp.sum_fintype, matExp]

/-- Matrix exponential preserves Hermitianness. -/
theorem matExp_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (matExp hA).IsHermitian :=
  hermFuncCalc_isHermitian Real.exp hA

/-- Matrix logarithm of a positive-definite matrix is Hermitian. -/
theorem matLog_isHermitian {A : Matrix n n ℂ} (hA : A.PosDef) :
    (matLog hA).IsHermitian :=
  hermFuncCalc_isHermitian Real.log hA.isHermitian

/-- `tr(exp(A)) = ∑ᵢ exp(λᵢ)` for Hermitian `A`. -/
theorem trace_matExp_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (matExp hA).trace = ∑ i, (Real.exp (hA.eigenvalues i) : ℂ) :=
  trace_hermFuncCalc_eq_sum Real.exp hA

/-- `exp(log(X)) = X` for positive-definite `X`.

**Gap**: requires spectral calculus functoriality — showing that the eigenbasis of
`hermFuncCalc f hA` is compatible with that of `A`, which needs a uniqueness result
for spectral decompositions not currently in Mathlib v4.28. -/
theorem matExp_matLog {X : Matrix n n ℂ} (hX : X.PosDef) :
    matExp (matLog_isHermitian hX) = X := by
  sorry

/-- `log(exp(A)) = A` for Hermitian `A`.

**Gap**: same spectral calculus functoriality as `matExp_matLog`. -/
theorem matLog_matExp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matLog (matExp_posDef hA) = A := by
  sorry

/-! ## Section 3: Hermitian Matrix Addition in Functional Calculus

For the statement of Lieb's theorem, we need to form `A + log X + s · log Y`
where `A` is Hermitian and `X, Y` are positive-definite. The sum of Hermitian
matrices is Hermitian. -/

section HermitianClosure

variable {m : Type*}

/-- Sum of Hermitian matrices is Hermitian. -/
theorem IsHermitian_add {A B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  hA.add hB

/-- Real scalar multiple of a Hermitian matrix is Hermitian. -/
theorem IsHermitian_smul {A : Matrix m m ℂ} (hA : A.IsHermitian) (s : ℝ) :
    (s • A).IsHermitian := by
  simp_all +decide [Matrix.IsHermitian, Matrix.conjTranspose_smul]

end HermitianClosure

/-! ## Section 4: Lieb's Concavity Theorem

### Statement

For fixed Hermitian `A : Matrix n n ℂ` and `s ∈ [0, 1]`, the map
  `Φ(X, Y) := tr exp(A + log X + s · log Y)`
is jointly concave on positive-definite matrices `X` and `Y`.

That is, for all positive-definite `X₁, X₂, Y₁, Y₂` and `t ∈ [0, 1]`:
  `Φ(t X₁ + (1-t) X₂, t Y₁ + (1-t) Y₂) ≥ t · Φ(X₁, Y₁) + (1-t) · Φ(X₂, Y₂)`

### Proof sketch (Lieb 1973)

The proof uses two key ingredients:
1. The **Peierls–Bogoliubov inequality**: for Hermitian `H`,
   `tr(exp(H)) ≥ exp(tr(H))` (after normalization).
2. **Epstein's theorem** / analytic interpolation: the map
   `s ↦ tr(X^s K Y^(1-s) K*)` is log-convex for `s ∈ [0,1]`.

From these, Lieb shows that `X ↦ tr(exp(A + log X))` is concave using
a variational representation of the trace exponential and Jensen's inequality
in the matrix sense. -/

/-- The Lieb functional: for Hermitian `A`, positive-definite `X`, `Y`,
    and `s ∈ [0,1]`, computes `tr exp(A + log X + s · log Y)`.

    This requires forming the Hermitian matrix `A + log X + s · log Y`,
    which is the sum of three Hermitian matrices. -/
noncomputable def liebFunctional
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {X : Matrix n n ℂ} (hX : X.PosDef)
    {Y : Matrix n n ℂ} (hY : Y.PosDef)
    (s : ℝ) : ℂ :=
  let logX := matLog hX
  let logY := matLog hY
  let H_herm : (A + logX + s • logY).IsHermitian :=
    (hA.add (matLog_isHermitian hX)).add (IsHermitian_smul (matLog_isHermitian hY) s)
  (matExp H_herm).trace

/-- **Lieb's Concavity Theorem** (Lieb 1973, Theorem 6).

For fixed Hermitian `A` and `s ∈ [0, 1]`, the map
`(X, Y) ↦ tr exp(A + log X + s · log Y)` is jointly concave on
positive-definite matrices.

Concretely: for positive-definite `X₁, X₂, Y₁, Y₂` and `t ∈ [0, 1]`:

    liebFunctional hA hXconv hYconv s ≥ₘ
      t • liebFunctional hA hX₁ hY₁ s + (1 - t) • liebFunctional hA hX₂ hY₂ s

where `hXconv` witnesses that `t • X₁ + (1 - t) • X₂` is positive-definite,
and similarly for `hYconv`.

**Gap**: The core analytic inequality requires either Epstein's interpolation
theorem or the Peierls–Bogoliubov inequality, neither of which is available
in Mathlib v4.28. -/
theorem lieb_concavity
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {X₁ X₂ : Matrix n n ℂ} (hX₁ : X₁.PosDef) (hX₂ : X₂.PosDef)
    {Y₁ Y₂ : Matrix n n ℂ} (hY₁ : Y₁.PosDef) (hY₂ : Y₂.PosDef)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hXconv : (t • X₁ + (1 - t) • X₂).PosDef)
    (hYconv : (t • Y₁ + (1 - t) • Y₂).PosDef) :
    ∃ (lhs rhs : ℂ),
      lhs = liebFunctional hA hXconv hYconv s ∧
      rhs = t • liebFunctional hA hX₁ hY₁ s + (1 - t) • liebFunctional hA hX₂ hY₂ s ∧
      (lhs - rhs).re ≥ 0 := by
  sorry

/-! ## Section 5: Corollaries for the Tropp Chain

These corollaries show how Lieb's theorem specializes to yield the
ingredients needed for the matrix Bernstein inequality. -/

/-- **Corollary (Lieb, s = 0)**: The map `X ↦ tr exp(A + log X)` is concave
    on positive-definite matrices. This is the key input for the Klein
    matrix inequality.

**Gap**: Follows from `lieb_concavity` with `s = 0`. -/
theorem lieb_concavity_s_eq_zero
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {X₁ X₂ : Matrix n n ℂ} (hX₁ : X₁.PosDef) (hX₂ : X₂.PosDef)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hXconv : (t • X₁ + (1 - t) • X₂).PosDef) :
    ∃ (lhs rhs : ℂ),
      lhs = liebFunctional hA hXconv hXconv 0 ∧
      rhs = t • liebFunctional hA hX₁ hX₁ 0 + (1 - t) • liebFunctional hA hX₂ hX₂ 0 ∧
      (lhs - rhs).re ≥ 0 := by
  sorry

/-- **Golden–Thompson inequality** (corollary of Lieb):
    For Hermitian `A, B`, `tr(exp(A + B)) ≤ tr(exp(A) · exp(B))`.
    This is used in the matrix MGF bounding step of Tropp's proof.

**Gap**: Requires the full Lieb machinery plus trace comparison inequalities. -/
theorem golden_thompson
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((matExp (hA.add hB)).trace - ((matExp hA) * (matExp hB)).trace).re ≤ 0 := by
  sorry

/-! ## Section 6: Summary of named gaps

The following sorry'd declarations constitute the honest gap inventory.
Each is individually provable given sufficient Mathlib infrastructure,
but that infrastructure is not present in Mathlib v4.28.

| Gap name | What's missing | Difficulty |
|---|---|---|
| `matExp_matLog` | Spectral calculus functoriality | Medium |
| `matLog_matExp` | Spectral calculus functoriality | Medium |
| `lieb_concavity` | Epstein interpolation / Peierls–Bogoliubov | Hard |
| `lieb_concavity_s_eq_zero` | Specialization of `lieb_concavity` | Easy (given above) |
| `golden_thompson` | Lieb machinery + trace inequalities | Hard |

### Downstream dependency chain

```
lieb_concavity
  └── lieb_concavity_s_eq_zero  (Klein matrix inequality input)
  └── golden_thompson           (matrix MGF bound input)
        └── Tropp matrix Bernstein concentration
```
-/

end MatrixLieb

end
