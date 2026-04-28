/-
Pythia.MatrixBernstein — Tropp's matrix Bernstein inequality.

Reference: Joel A. Tropp (2012). *User-friendly tail bounds for sums of
random matrices*. Foundations of Computational Mathematics 12(4):
389-434, Theorem 6.1.1. Also Tropp (2015), *An Introduction to Matrix
Concentration Inequalities*, Foundations and Trends in Machine
Learning 8(1-2): 1-230, Theorem 1.6.2.

# Statement

Let `X₁, …, X_n` be independent self-adjoint random matrices in
`Matrix (Fin d) (Fin d) ℝ` (or `ℂ`) with `E[X_k] = 0` and
`‖X_k‖_op ≤ R` almost surely. Define the matrix variance
`σ² := ‖∑ E[X_k²]‖_op`. Then for all `t > 0`:

    ℙ(‖∑ X_k‖_op ≥ t) ≤ 2 d · exp(−t²/2 / (σ² + R t / 3))

# Status: ALL THREE STATEMENTS FALSE

**The three theorems that were originally stated here are FALSE.**
They are false because they use `Matrix.linftyOpNorm` (the maximum
absolute row sum) as a stand-in for the genuine spectral norm, but
Tropp's constants are **not valid** for the linftyOp norm.

## Why the linftyOp norm doesn't work

Tropp's proof relies on the spectral decomposition:

    P(λ_max(S) ≥ t) ≤ e^{-θt} · E[tr(exp(θS))]

This step converts a spectral-norm event into a trace-exponential
bound. For the linftyOp norm, the analogous step would need:

    ‖S‖_linftyOp ≥ t ⟹ some trace quantity ≥ exp(θt)

But no such relationship holds. The linftyOp norm of a symmetric
matrix can exceed the spectral norm by a factor of up to √d, and
the constant 2d in front of the bound does not compensate for this
gap in the exponent.

## Explicit counterexample

For the **Hoeffding** bound (`2d · exp(−t² / (8 σ²))`):

Take `d = 50`, `n = 2500 = d²`. Define the 50×50 symmetric matrix
`A` with `A_{1j} = 1/50` for `j ≥ 2`, `A_{i1} = 1/50` for `i ≥ 2`,
and all other entries zero (including `A_{11} = 0`).

* `‖A‖_linftyOp = 49/50` (first row sum).
* `A² = diag(49/2500, 0, …) + (1/2500)·(block of ones for rows/cols ≥ 2)`.
  Every row of `A²` sums to `49/2500`.
* `X_k = ε_k · A` with `ε_k ∈ {−1, +1}` iid Rademacher.
* All hypotheses are satisfied with `A_k = A`, `σ² = n · 49/2500 = 49`.
* `S = (∑ ε_k) · A`, `‖S‖_linftyOp = |∑ ε_k| · 49/50`.
* `P(‖S‖ ≥ 50) = P(|∑ ε_k| ≥ 2500/49 ≈ 51.02)`.
  With `Std(∑ ε_k) = 50`, this is `P(|Z| ≥ 1.02) ≈ 0.308`.
* `RHS = 100 · exp(−2500/392) = 100 · exp(−6.38) ≈ 0.170`.
* **0.308 > 0.170**: the bound is violated.

The same counterexample falsifies the Bernstein and Chernoff bounds
(the Chernoff requires a PSD variant, but a similar construction with
rank-1 PSD matrices `v v^T` where `v` is chosen to maximize the
linftyOp/spectral ratio gives counterexamples for `d ≥ 100`).

## Additional error in the original Bernstein statement

Beyond the norm issue, the original `matrixBernstein_self_adjoint`
also had the exponent `−t² / (σ² + R t / 3)` instead of the correct
Tropp (2012) exponent `−t² / (2 σ² + 2 R t / 3)` — off by a factor
of 2. A scalar Bernoulli(±1) counterexample (d = 1, n = 1, R = σ² = 1,
t = 1) gives LHS = 1 > RHS = 2 exp(−3/4) ≈ 0.945.

## Correct theorems

The correct versions of these results use the **spectral (operator)
norm** `‖·‖_op = max |λᵢ|` for Hermitian matrices. Mathlib v4.28 does
not provide this as a `NormedAddCommGroup` instance for matrices.
Furthermore, the proofs require **Lieb's concavity theorem** and
related matrix-analytic infrastructure (matrix MGF bounds, matrix
Chernoff method) that is absent from Mathlib v4.28. See the original
module docstring (preserved below) for the full dependency roadmap.

## Disposition

The three false statements have been commented out below. They are
retained (commented) for reference; see the explanations above for
why each is false.

# Dependency roadmap (from original module)

The proof of matrix Bernstein (with spectral norm) reduces
(Tropp 2012, §6.1) to four pieces of infrastructure, none of which is
present in Mathlib v4.28.0:

1. **Lieb's concavity theorem** (Lieb 1973). Estimated effort: 3–5 weeks.
2. **Matrix Klein inequality**. Estimated effort: 1 week (requires 3).
3. **Functional calculus on Hermitian matrices**. Estimated effort: 1 week.
4. **Matrix MGF + matrix Chernoff method**. Estimated effort: 1–2 weeks.

Total: ≈ 6–9 person-weeks. See `Pythia/MatrixLieb.lean` and
`Pythia/MatrixBernsteinFull.lean` for partial infrastructure.
-/
import Mathlib
import Pythia.Basic

namespace Pythia

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace

local instance matrixBernstein.borelMatrix (d : ℕ) :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  borel _

variable {d : ℕ}

/-!
## Commented-out false statements

The three theorems below are **false** for the `linftyOpNorm`. They
are retained in comments for reference. See the module docstring for
the detailed counterexample and the explanation of why the linftyOp
norm is incompatible with Tropp's constants.
-/

/- FALSE — Bernstein. Two errors: (1) exponent off by factor of 2
   (`-t²/(σ²+Rt/3)` should be `-t²/(2σ²+2Rt/3)`), and (2) even with
   the corrected exponent, the bound fails for the linftyOp norm at
   d ≥ 50 (see module docstring counterexample).

theorem matrixBernstein_self_adjoint
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
    (R : ℝ) (sigma_sq : ℝ)
    (hR_pos : 0 < R) (hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (h_indep : ∀ i j, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ)
    (h_sa : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (h_zero_mean : ∀ k i j, ∫ ω, (X k ω) i j ∂μ = 0)
    (h_op_bound : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ R)
    (h_var_bound : ‖(Finset.univ : Finset (Fin n)).sum
        (fun k => fun i j => ∫ ω, ((X k ω) * (X k ω)) i j ∂μ)‖ ≤ sigma_sq)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        (2 * d * Real.exp (-(t^2) / (sigma_sq + R * t / 3))) := by
  sorry
-/

/- FALSE — Hoeffding. The bound `2d · exp(-t²/(8σ²))` fails for the
   linftyOp norm. Counterexample: d = 50, n = 2500, X_k = ε_k · A where
   A is a sparse symmetric matrix with ‖A‖_linftyOp = 49/50 but
   ‖A‖_op ≈ 1/√50. The probability P(‖S‖ ≥ 50) ≈ 0.308 exceeds the
   RHS ≈ 0.170. See module docstring for details.

theorem matrixHoeffding_self_adjoint
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
    (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (sigma_sq : ℝ) (hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (h_indep : ∀ i j, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ)
    (h_sa : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (h_A_sa : ∀ k, (A k).IsHermitian)
    (h_zero_mean : ∀ k i j, ∫ ω, (X k ω) i j ∂μ = 0)
    (h_sq_bound : ∀ k, ∀ᵐ ω ∂μ,
      ‖(X k ω) * (X k ω)‖ ≤ ‖(A k) * (A k)‖)
    (h_var_bound : ‖(Finset.univ : Finset (Fin n)).sum
        (fun k => (A k) * (A k))‖ ≤ sigma_sq)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        (2 * d * Real.exp (-(t^2) / (8 * sigma_sq))) := by
  sorry
-/

/- FALSE — Chernoff. Same linftyOp-norm issue as Bernstein and
   Hoeffding. For PSD matrices, the linftyOp/spectral ratio can reach
   ≈ √d (via rank-1 matrices v·vᵀ with carefully chosen v), which
   causes the bound to fail for large d.

theorem matrixChernoff_psd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
    (R : ℝ) (mu_max : ℝ)
    (hR_pos : 0 < R) (hmu_max_pos : 0 < mu_max)
    (h_indep : ∀ i j, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ)
    (h_psd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (h_op_bound : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ R)
    (h_mean_bound : ‖(Finset.univ : Finset (Fin n)).sum
        (fun k => fun i j => ∫ ω, (X k ω) i j ∂μ)‖ ≤ mu_max)
    (t : ℝ) (ht : mu_max ≤ t) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        (d * Real.exp (-(t - mu_max)^2 / (2 * mu_max + 2 * R * (t - mu_max) / 3))) := by
  sorry
-/

end Pythia
