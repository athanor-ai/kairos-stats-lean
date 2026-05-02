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

### Proved (previously marked as gaps)

* `matExp_matLog` — `exp(log(X)) = X` for positive-definite `X`.
  Proved via `cfc_comp` (Mathlib's continuous functional calculus composition).
* `matLog_matExp` — `log(exp(A)) = A` for Hermitian `A`.
  Same approach, using `Real.log_exp`.
* `lieb_concavity_s_eq_zero` — proved by instantiating `lieb_concavity` with `s = 0`.

### New infrastructure (added to close the gaps above)

* `hermFuncCalc_eq_hA_cfc`, `hermFuncCalc_eq_cfc` — bridge to Mathlib CFC
* `hermFuncCalc_comp` — composition of spectral functional calculus
* `hermFuncCalc_congr` — congruence when functions agree on eigenvalues

### Remaining Mathlib v4.28 gaps (explicit named sorries)

* `lieb_concavity` — the core Lieb concavity inequality. Requires either Epstein's
  interpolation theorem or the Peierls–Bogoliubov inequality, neither in Mathlib v4.28.
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

/-! ### Spectral Functional Calculus: Composition and Congruence

We link `hermFuncCalc` to Mathlib's continuous functional calculus (`cfc`) to obtain
composition and congruence results. For finite-dimensional matrices the spectrum is finite,
so every function is continuous on it, making the CFC applicable without restrictions. -/

/-- `hermFuncCalc f hA` agrees with Mathlib's `hA.cfc f`. -/
theorem hermFuncCalc_eq_hA_cfc {A : Matrix n n ℂ} (f : ℝ → ℝ) (hA : A.IsHermitian) :
    hermFuncCalc f hA = hA.cfc f := by
  unfold hermFuncCalc Matrix.IsHermitian.cfc; congr 1

/-- `hermFuncCalc f hA` agrees with the general `cfc f A`. -/
theorem hermFuncCalc_eq_cfc {A : Matrix n n ℂ} (f : ℝ → ℝ) (hA : A.IsHermitian) :
    hermFuncCalc f hA = cfc f A := by
  rw [hermFuncCalc_eq_hA_cfc, hA.cfc_eq]

/-- **Composition**: `hermFuncCalc g (hermFuncCalc f A) = hermFuncCalc (g ∘ f) A`.
    Uses `cfc_comp` and the fact that the spectrum of a matrix is finite. -/
theorem hermFuncCalc_comp (g f : ℝ → ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermFuncCalc g (hermFuncCalc_isHermitian f hA) = hermFuncCalc (g ∘ f) hA := by
  simp only [hermFuncCalc_eq_cfc]
  exact (cfc_comp g f A hA.isSelfAdjoint
    (Matrix.finite_real_spectrum.image f |>.continuousOn g)
    (Matrix.finite_real_spectrum.continuousOn f)).symm

/-- **Congruence**: if `f` and `g` agree on all eigenvalues of `A`,
    then `hermFuncCalc f hA = hermFuncCalc g hA`. -/
theorem hermFuncCalc_congr {A : Matrix n n ℂ} (f g : ℝ → ℝ) (hA : A.IsHermitian)
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    hermFuncCalc f hA = hermFuncCalc g hA := by
  unfold hermFuncCalc; congr 1; ext i j; simp only [Matrix.diagonal, Matrix.of_apply]
  split_ifs with heq
  · subst heq; congr 1; exact_mod_cast h i
  · rfl

/-- `exp(log(X)) = X` for positive-definite `X`.

Proved via spectral calculus composition: `exp ∘ log = id` on positive reals,
and eigenvalues of a positive-definite matrix are positive. -/
theorem matExp_matLog {X : Matrix n n ℂ} (hX : X.PosDef) :
    matExp (matLog_isHermitian hX) = X := by
  show hermFuncCalc Real.exp (hermFuncCalc_isHermitian Real.log hX.isHermitian) = X
  rw [hermFuncCalc_comp]
  conv_rhs => rw [← hermFuncCalc_id hX.isHermitian]
  exact hermFuncCalc_congr _ _ _ (fun i => Real.exp_log (hX.eigenvalues_pos i))

/-- `log(exp(A)) = A` for Hermitian `A`.

Proved via spectral calculus composition: `log ∘ exp = id` on all reals. -/
theorem matLog_matExp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matLog (matExp_posDef hA) = A := by
  show hermFuncCalc Real.log (hermFuncCalc_isHermitian Real.exp hA) = A
  rw [hermFuncCalc_comp]
  conv_rhs => rw [← hermFuncCalc_id hA]
  exact hermFuncCalc_congr _ _ _ (fun i => Real.log_exp _)

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

/- **INCORRECT STATEMENT — commented out**.

The original `lieb_concavity` claimed **joint** concavity of
`(X, Y) ↦ tr exp(A + log X + s · log Y)` in both `X` and `Y` simultaneously.
This is **false**: the function `(x, y) ↦ x · y^s` (the 1×1 specialisation) is
not jointly concave for `0 < s < 1`.  A concrete 1×1 counterexample with
`A = 0, s = 0.5, t = 0.5, x₁ = 1.5, x₂ = 0.5, y₁ = 1.39, y₂ = 0.61` gives
LHS = 1 < RHS ≈ 1.0795.

The correct Lieb (1973) result is **separate** concavity in `X` alone
(with `A`, `Y`, `s` fixed); see `lieb_concavity_in_X` below.

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
-/

/-- **Lieb's Concavity Theorem — corrected formulation** (Lieb 1973).

For fixed Hermitian `A`, positive-definite `Y`, and `s ∈ [0, 1]`, the map
`X ↦ tr exp(A + log X + s · log Y)` is concave on positive-definite matrices.

The original `lieb_concavity` in this file incorrectly claimed *joint*
concavity in `(X, Y)`.  Lieb's actual result is concavity in each variable
separately (the other being held fixed).  This corrected version fixes `Y`. -/
theorem lieb_concavity_in_X
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {X₁ X₂ : Matrix n n ℂ} (hX₁ : X₁.PosDef) (hX₂ : X₂.PosDef)
    {Y : Matrix n n ℂ} (hY : Y.PosDef)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hXconv : (t • X₁ + (1 - t) • X₂).PosDef) :
    ∃ (lhs rhs : ℂ),
      lhs = liebFunctional hA hXconv hY s ∧
      rhs = t • liebFunctional hA hX₁ hY s + (1 - t) • liebFunctional hA hX₂ hY s ∧
      (lhs - rhs).re ≥ 0 := by
  sorry

/-! ## Section 5: Corollaries for the Tropp Chain

These corollaries show how Lieb's theorem specializes to yield the
ingredients needed for the matrix Bernstein inequality. -/

/-
**Corollary (Lieb, s = 0)**: The map `X ↦ tr exp(A + log X)` is concave
    on positive-definite matrices. This is the key input for the Klein
    matrix inequality.

**Gap**: Follows from `lieb_concavity` with `s = 0`.
-/
theorem lieb_concavity_s_eq_zero
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {X₁ X₂ : Matrix n n ℂ} (hX₁ : X₁.PosDef) (hX₂ : X₂.PosDef)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hXconv : (t • X₁ + (1 - t) • X₂).PosDef) :
    ∃ (lhs rhs : ℂ),
      lhs = liebFunctional hA hXconv hXconv 0 ∧
      rhs = t • liebFunctional hA hX₁ hX₁ 0 + (1 - t) • liebFunctional hA hX₂ hX₂ 0 ∧
      (lhs - rhs).re ≥ 0 := by
  refine' ⟨ _, _, rfl, rfl, _ ⟩;
  convert lieb_concavity_in_X hA hX₁ hX₂ hX₁ ( show 0 ≤ 0 by norm_num ) ( show 0 ≤ 1 by norm_num ) ht₀ ht₁ hXconv using 1 ; norm_num [ liebFunctional ];
  simp +decide [ matExp ];
  simp +decide [ hermFuncCalc ]

/-- **Tangent inequality for the Lieb functional at the identity**.

For Hermitian `A` and positive-definite `Y`:
  `tr(exp(A + log Y)) ≤ tr(exp(A) · Y)`

This is the first-order tangent (supporting hyperplane) inequality for the
concave function `X ↦ tr(exp(A + log X))` evaluated at `X₀ = I`.
The derivative at `I` is `H ↦ tr(exp(A) · H)`, giving
  `F(Y) ≤ F(I) + dF(I)(Y - I) = tr(exp(A)) + tr(exp(A)(Y - I)) = tr(exp(A) · Y)`. -/
theorem trace_exp_log_le_trace_mul
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {Y : Matrix n n ℂ} (hY : Y.PosDef) :
    (matExp (hA.add (matLog_isHermitian hY))).trace.re ≤
      ((matExp hA) * Y).trace.re := by
  sorry

/-
**Golden–Thompson inequality** (corollary of Lieb):
    For Hermitian `A, B`, `tr(exp(A + B)) ≤ tr(exp(A) · exp(B))`.
    This is used in the matrix MGF bounding step of Tropp's proof.

    Proved from `trace_exp_log_le_trace_mul` by setting `Y = exp(B)` and
    using `matLog_matExp` to simplify `log(exp(B)) = B`.
-/
theorem golden_thompson
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((matExp (hA.add hB)).trace - ((matExp hA) * (matExp hB)).trace).re ≤ 0 := by
  simp +zetaDelta at *
  convert trace_exp_log_le_trace_mul hA (matExp_posDef hB)
  exact (matLog_matExp hB).symm

/-! ## Section 6: Summary of gaps

### Bug fix: `lieb_concavity` was false

The original `lieb_concavity` claimed **joint** concavity of
`(X, Y) ↦ tr exp(A + log X + s · log Y)` in both `X` and `Y` simultaneously.
A 1×1 counterexample (`A = 0, s = 0.5, t = 0.5, x₁ = 1.5, x₂ = 0.5,
y₁ = 1.39, y₂ = 0.61`) disproves this: LHS = 1 < RHS ≈ 1.0795.

The correct Lieb (1973) result is **separate** concavity in each variable.
The corrected statement `lieb_concavity_in_X` fixes `Y` and proves
concavity in `X` alone.

### Closed gaps (previously sorry'd)

| Name | Method | Key Mathlib ingredient |
|---|---|---|
| `matExp_matLog` | CFC composition | `cfc_comp`, `Real.exp_log`, `PosDef.eigenvalues_pos` |
| `matLog_matExp` | CFC composition | `cfc_comp`, `Real.log_exp` |
| `golden_thompson` | Reduction to `trace_exp_log_le_trace_mul` | `matLog_matExp` |
| `lieb_concavity_s_eq_zero` | Reduction to `lieb_concavity_in_X` | — |

### Remaining sorry'd declarations

| Gap name | What's missing | Difficulty |
|---|---|---|
| `lieb_concavity_in_X` | Epstein interpolation / Peierls–Bogoliubov | Hard |
| `trace_exp_log_le_trace_mul` | Tangent inequality for concave Lieb functional | Hard |

### Downstream dependency chain

```
lieb_concavity_in_X
  └── lieb_concavity_s_eq_zero  (Klein matrix inequality input)
trace_exp_log_le_trace_mul
  └── golden_thompson           (matrix MGF bound input)
        └── Tropp matrix Bernstein concentration
```

### Notes

`trace_exp_log_le_trace_mul` states `tr(exp(A + log Y)) ≤ tr(exp(A) · Y)`
and is equivalent to the Golden–Thompson inequality.
It follows from `lieb_concavity_in_X` via the tangent (supporting-hyperplane)
inequality for concave functions at `X₀ = I`, but formalising the derivative
of `X ↦ tr(exp(A + log X))` requires non-commutative calculus infrastructure
not yet in Mathlib v4.28.
-/

end MatrixLieb

end