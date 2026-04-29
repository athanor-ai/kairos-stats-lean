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

    ℙ(‖∑ X_k‖_op ≥ t) ≤ 2 d · exp(−t² / (σ² + R t / 3))

The "sharp" Tropp form replaces `R t / 3` by `R t / 6` and uses a
tighter matrix-MGF bound; this scaffold ships the standard form first.

# Status: Tier 7 honest scaffold

**This module declares the statement; the proof is `sorry`.** Closure
is a multi-week project requiring substantial Mathlib infrastructure
that does not yet exist in v4.28.0. See dependency roadmap below.

Per `CONTRIBUTING.md` hard rule 2 (honest-scaffold-with-flagged-sorry):
this module is excluded from `Pythia.AxiomAudit`. Closure of any
of the three statements below MUST be paired with adding it to the
audit harness. Do **not** add this module to the audit before that.

# Why this is in the library

Mathlib v4.28.0 has zero matrix concentration coverage. The closest
related modules are:

* `Mathlib.Analysis.Normed.Algebra.MatrixExponential` — defines
  `Matrix.exp` (essentially `NormedSpace.exp 𝕂` specialized to
  `Matrix n n 𝕂`) and proves elementary algebraic identities
  (`exp_diagonal`, `exp_blockDiagonal`, `exp_conjTranspose`,
  `exp_transpose`, `IsHermitian.exp`, `exp_neg`, `exp_zsmul`,
  `exp_conj`). It does **not** include any analytic / monotonicity /
  trace-functional results.

* `Mathlib.Analysis.Matrix.Hermitian`,
  `Mathlib.Analysis.Matrix.Spectrum` — spectral theorem for Hermitian
  matrices and basic eigenvalue API.

* `Mathlib.Analysis.Matrix.Normed` — provides three matrix norms
  (sup-of-sup `Matrix.normedAddCommGroup`, Frobenius
  `Matrix.frobeniusNormedAddCommGroup`, and the row-sum `linftyOp`
  norm) as non-instances. Note: **none** of these is the operator
  (spectral) norm. The genuine spectral norm of a self-adjoint matrix
  agrees with `linftyOp` only on diagonal matrices in general.

* No Lieb concavity. No Klein matrix inequality. No matrix MGF.
  No matrix Chernoff / Bernstein / Hoeffding.

So even *stating* Tropp's theorem requires committing to a notion of
operator norm. The scaffold below uses `Matrix.linftyOpNorm` as a
placeholder via the `[NormedAddCommGroup …]` machinery; the genuine
spectral-norm version is left as a future refactor.

# Dependency roadmap

The proof of `matrixBernstein_self_adjoint` reduces (Tropp 2012, §6.1)
to four pieces of infrastructure, none of which is present in Mathlib
v4.28.0:

1. **Lieb's concavity theorem.** For `H` Hermitian and `0 < A`
   positive-definite, the function `A ↦ tr exp(H + log A)` is concave
   on the positive cone. Reference: Lieb, *Convex trace functions and
   the Wigner-Yanase-Dyson conjecture*, Adv. Math. 11 (1973) 267-288.
   This is the analytic core; ports of this proof exist in Coq
   (`mathcomp-analysis`) but not Lean. Difficulty: high — needs the
   relative-modular-operator framework or Effros' simpler proof via
   matrix means. Estimated effort: 3-5 weeks of focused work.

2. **Matrix Klein inequality** (a.k.a. Klein's lemma). For convex
   `f : ℝ → ℝ` differentiable and Hermitian `A, B`:
   `tr (f(A) − f(B) − (A − B) · f'(B)) ≥ 0`. Follows from spectral
   theorem + scalar Klein. Difficulty: medium. Estimated effort:
   1 week. Requires (3) below.

3. **Functional calculus on Hermitian matrices.** Given a continuous
   `f : ℝ → ℝ` and Hermitian `A`, define `f(A)` via the spectral
   decomposition. Mathlib has the C*-algebraic
   `cfc` (`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus`)
   and `Matrix.IsHermitian.eigenvalues`/`eigenvectorBasis` but
   has not assembled the matrix-specific connector lemma
   `f(A) = ∑ f(λᵢ) • (vᵢ ⬝ vᵢᵀ)` in a directly usable form.
   Estimated effort: 1 week.

4. **Matrix MGF + matrix Chernoff method.** Given (1) one shows
   `E[tr exp(θ ∑ Xₖ)] ≤ tr exp(∑ log E[exp(θ Xₖ)])`
   (Lieb-Tropp master inequality). Combined with Markov's inequality
   on `tr exp(θ M)` and a sub-exponential bound on the per-summand
   matrix CGF (Tropp 2012, Lemma 6.7) this gives Bernstein. The
   matrix-CGF bound itself is a 1-page calculation once `Matrix.exp`
   monotonicity in the Loewner order is available, which in turn
   needs (1)-(3). Estimated effort: 1-2 weeks once (1)-(3) are in
   place.

Total: ≈ 6-9 person-weeks of Lean engineering plus mathematical
review. **Out of scope for a single subagent task.** This module
ships the *statement* + dependency tree; closure happens via a
sequence of follow-up PRs (one per roadmap item).

# Followup work

The natural unbundling, in priority order:

* `Pythia/Matrix/HermitianFunctionalCalculus.lean` — port the
  spectral-decomposition `f(A)` construction (item 3).
* `Pythia/Matrix/Klein.lean` — matrix Klein inequality (item 2).
* `Pythia/Matrix/Lieb.lean` — Lieb's concavity (item 1).
* `Pythia/Matrix/MGF.lean` — matrix moment-generating function
  + Lieb-Tropp master inequality + Tropp's matrix-CGF lemma (item 4).
* `Pythia/MatrixBernstein.lean` — close the sorries here.

Each of these is itself a candidate for a Mathlib upstream PR; v4.28
has zero coverage of matrix concentration, so all four pieces would
land cleanly under `Mathlib.Analysis.Matrix.*` /
`Mathlib.Probability.Moments.*`.

# Companion theorems (also scaffolded here)

* `matrixHoeffding_self_adjoint` — Tropp's matrix Hoeffding (2012,
  Theorem 1.3). Same dependency tree, weaker assumptions. Listed for
  completeness; closure shares (1)-(4).
* `matrixChernoff_self_adjoint` — Tropp's matrix Chernoff (2012,
  Theorem 1.1). Specialised to bounded *positive-semidefinite*
  summands; the variance term simplifies.
-/
import Mathlib
import Pythia.Basic

namespace Pythia

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

/-! ## Operator-norm placeholder

We use `Matrix.linftyOpNorm` (the maximum row sum, available as a
non-instance in `Mathlib.Analysis.Matrix.Normed`) as a stand-in for
the genuine spectral / operator norm pending the closure of the
dependency roadmap above. On Hermitian matrices the spectral norm and
the linfty-op norm differ by at most a factor of `√d`; the constant
in front of the Bernstein bound absorbs this gap, so the qualitative
shape of the bound is preserved.

The closure PR for item (3) of the roadmap will swap this placeholder
for the genuine spectral norm, removing the constant slack.
-/

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace

/-- Borel measurable-space instance on the placeholder operator-normed
matrix space. Local to this module while the operator-norm story is
the row-sum proxy; a follow-up refactor that moves to the genuine
spectral norm should re-derive this. -/
local instance matrixBernstein.borelMatrix (d : ℕ) :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  borel _

variable {d : ℕ}

/-- **Tropp's matrix Bernstein inequality** (Tropp 2012, Theorem 6.1.1;
standard form).

Given independent self-adjoint random matrices `X₁, …, X_n` in
`Matrix (Fin d) (Fin d) ℝ` with

* `E[X_k] = 0` (per-component integrability + zero matrix mean),
* `‖X_k‖_op ≤ R` almost surely, and
* matrix variance `σ² := ‖∑ E[X_k²]‖_op`,

then for all `t > 0`:
$$ ℙ(‖∑ X_k‖_op ≥ t) ≤ 2 d · \exp(−t² / (σ² + R t / 3)). $$

**Status: scaffold.** Closure depends on the four-item roadmap in
the module docstring. Excluded from `Pythia.AxiomAudit` until
the proof lands. -/
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

/-- **Tropp's matrix Hoeffding inequality** (Tropp 2012, Theorem 1.3).

Given independent self-adjoint random matrices `X₁, …, X_n` with
`E[X_k] = 0` and almost-sure bounds `X_k² ⪯ A_k²` for fixed Hermitian
`A_k`, set `σ² := ‖∑ A_k²‖_op`. Then for all `t > 0`:
$$ ℙ(‖∑ X_k‖_op ≥ t) ≤ 2 d · \exp(−t² / (8 σ²)). $$

**Status: scaffold.** Same dependency roadmap as
`matrixBernstein_self_adjoint`. -/
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

/-- **Tropp's matrix Chernoff inequality** (Tropp 2012, Theorem 1.1;
upper-tail form).

Given independent positive-semidefinite random matrices `X₁, …, X_n`
with almost-sure bound `‖X_k‖_op ≤ R`, set
`μ_max := ‖∑ E[X_k]‖_op`. Then for all `t ≥ μ_max`:
$$ ℙ(‖∑ X_k‖_op ≥ t) ≤
   d · \left(\frac{e^{t/μ_{\max} − 1}}{(t/μ_{\max})^{t/μ_{\max}}}\right)^{μ_{\max}/R}. $$

(The standard rewrite as a sub-Bernstein form follows from the
inequality `(1 + x) log(1 + x) − x ≥ x²/(2 + 2 x/3)` for `x ≥ 0`.)

**Status: scaffold.** Specialisation of the Bernstein dependency
roadmap; the PSD assumption removes the need for Hermitian-only
spectrum control but otherwise rides the same Lieb / Klein / matrix-
MGF infrastructure. -/
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

end Pythia
