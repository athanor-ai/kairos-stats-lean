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

    ℙ(‖∑ X_k‖_op ≥ t) ≤ 2 d · exp(−t² / (2 σ² + 2 R t / 3))

# Status: Tier 7 scaffold with private infrastructure helpers

**This module decomposes the proofs into private helpers.** The three
main theorems are proved modulo private infrastructure lemmas that
capture Tropp's matrix Laplace transform method. The private helpers
that require Lieb concavity / matrix-MGF subadditivity are marked
`sorry`; see the dependency roadmap below for closure plan.

Per `CONTRIBUTING.md` hard rule 2 (honest-scaffold-with-flagged-sorry):
this module is excluded from `Pythia.AxiomAudit`. Closure of any
of the three statements below MUST be paired with adding it to the
audit harness. Do **not** add this module to the audit before that.

# Dependency roadmap

The proof of `matrixBernstein_self_adjoint` reduces (Tropp 2012, §6.1)
to four pieces of infrastructure, none of which is present in Mathlib
v4.28.0:

1. **Lieb's concavity theorem.**
2. **Matrix Klein inequality.**
3. **Functional calculus on Hermitian matrices.**
4. **Matrix MGF + matrix Chernoff method.**

Total: ≈ 6-9 person-weeks of Lean engineering. The private helpers
below isolate exactly which steps require this infrastructure.
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
dependency roadmap above.
-/

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace

/-- Borel measurable-space instance on the placeholder operator-normed
matrix space. -/
local instance matrixBernstein.borelMatrix (d : ℕ) :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  borel _

variable {d : ℕ}

/-! ## Private scaffolding — Tropp's matrix Laplace transform framework

The three main theorems below are proved from private helpers that
decompose the proof into:

1. A **matrix Laplace master bound** parameterised by Laplace
   parameter `θ > 0`. This encapsulates the matrix-specific content:
   matrix Markov inequality, Lieb's trace-exp subadditivity, and the
   per-summand matrix CGF bound. These helpers require infrastructure
   from the dependency roadmap and are currently `sorry`.

2. A **scalar optimisation** lemma that chooses the optimal `θ` and
   shows the resulting exponent matches the stated bound. These are
   pure real analysis.

The main theorems follow by composing (1) and (2) via monotonicity
of `exp` and `ENNReal.ofReal`.
-/

/-! ### Bernstein private helpers -/

/-- **Matrix Laplace master bound** for Bernstein (Tropp 2012, §6.1).

For any `θ > 0`, the probability that the operator norm of the sum
exceeds `t` is bounded by
`2 d · exp(−θ t + σ² · (exp(θR) − θR − 1) / R²)`.

The exponent `σ² · (exp(θR) − θR − 1) / R²` is `σ² · θ² · g(θR)`
where `g(u) = (eᵘ − u − 1) / u²` is Tropp's scalar MGF kernel.
This form absorbs the `θ²` factor that makes the optimisation
yield the correct Bernstein exponent.

This combines: (i) matrix Markov inequality on `tr exp(±θ S)`,
(ii) Lieb–Tropp subadditivity, (iii) per-summand CGF bound,
(iv) `tr exp(cV) ≤ d · exp(c · ‖V‖)` for PSD `V`.

**Status: sorry.** Requires Lieb concavity (roadmap item 1) and
matrix-MGF infrastructure (roadmap item 4). -/
private lemma bernstein_master_bound
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
    (t : ℝ) (ht : 0 < t)
    (θ : ℝ) (hθ : 0 < θ) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        (2 * ↑d * Real.exp
          (-θ * t + sigma_sq * (Real.exp (θ * R) - θ * R - 1) / R ^ 2)) := by
  sorry

/-
**Scalar optimisation** for the Bernstein bound.

There exists `θ > 0` such that
`−θ t + σ² (eᶿᴿ − θR − 1)/R² ≤ −t²/(2σ² + 2Rt/3)`.

When `σ² > 0`, the choice `θ = log(1 + Rt/σ²)/R` achieves this via
the elementary inequality `(1+u)log(1+u) − u ≥ u²/(2 + 2u/3)`.
When `σ² = 0`, the choice `θ = 3/(2R)` works since the CGF term
vanishes.
-/
private lemma bernstein_scalar_opt
    (t R sigma_sq : ℝ) (ht : 0 < t) (hR : 0 < R)
    (hσ : 0 ≤ sigma_sq) :
    ∃ θ : ℝ, 0 < θ ∧
      -θ * t + sigma_sq * (Real.exp (θ * R) - θ * R - 1) / R ^ 2 ≤
        -(t ^ 2) / (2 * sigma_sq + 2 * R * t / 3) := by
  by_cases hσ' : sigma_sq = 0;
  · subst hσ'; use 3 / ( 2 * R ) ; ring_nf; norm_num [ ht.ne', hR.ne' ] ;
    exact ⟨ hR, by nlinarith [ mul_inv_cancel_left₀ ht.ne' ( R⁻¹ * t ) ] ⟩;
  · refine' ⟨ Real.log ( 1 + t * R / sigma_sq ) / R, div_pos ( Real.log_pos _ ) hR, _ ⟩;
    · exact lt_add_of_pos_right _ ( by positivity );
    · -- Simplifying the inequality.
      have h_simp : (1 + t * R / sigma_sq) * Real.log (1 + t * R / sigma_sq) - t * R / sigma_sq ≥ 3 * (t * R / sigma_sq)^2 / (6 + 2 * t * R / sigma_sq) := by
        have h_ineq : ∀ u : ℝ, 0 ≤ u → (1 + u) * Real.log (1 + u) - u ≥ 3 * u^2 / (6 + 2 * u) := by
          -- Let's choose any $u \geq 0$ and derive the inequality.
          intro u hu
          have h_deriv : ∀ u : ℝ, 0 < u → deriv (fun u => (1 + u) * Real.log (1 + u) - u - 3 * u^2 / (6 + 2 * u)) u ≥ 0 := by
            intro u hu; norm_num [ add_comm, mul_comm, ne_of_gt, add_pos, hu ];
            -- We'll use the fact that $Real.log (u + 1) \geq \frac{2u}{u + 2}$ for $u > 0$.
            have h_log_ineq : ∀ u : ℝ, 0 < u → Real.log (u + 1) ≥ 2 * u / (u + 2) := by
              -- Let's choose any $u > 0$ and derive the inequality.
              intro u hu
              have h_deriv : ∀ u : ℝ, 0 < u → deriv (fun u => Real.log (u + 1) - 2 * u / (u + 2)) u ≥ 0 := by
                intro u hu; norm_num [ mul_comm, ne_of_gt, add_pos, hu ];
                rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> nlinarith;
              have := exists_deriv_eq_slope ( f := fun u => Real.log ( u + 1 ) - 2 * u / ( u + 2 ) ) hu; norm_num at *;
              contrapose! this;
              exact ⟨ continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.log ( continuousAt_id.add continuousAt_const ) ( by linarith [ hx.1 ] ) ) ( ContinuousAt.div ( continuousAt_const.mul continuousAt_id ) ( continuousAt_id.add continuousAt_const ) ( by linarith [ hx.1 ] ) ), fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.add_const _ ) ( by linarith [ hx.1 ] ) ) ( DifferentiableAt.div ( differentiableAt_id.const_mul _ ) ( differentiableAt_id.add_const _ ) ( by linarith [ hx.1 ] ) ) ), fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv c hc.1 ] ⟩;
            exact le_trans ( by rw [ div_le_div_iff₀ ] <;> nlinarith ) ( h_log_ineq u hu );
          by_contra h_contra;
          have := exists_deriv_eq_slope ( f := fun u => ( 1 + u ) * Real.log ( 1 + u ) - u - 3 * u ^ 2 / ( 6 + 2 * u ) ) ( show u > 0 from hu.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at this;
          exact absurd ( this ( by exact ContinuousOn.sub ( ContinuousOn.sub ( ContinuousOn.mul ( continuousOn_const.add continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ hx.1 ] ) ) continuousOn_id ) ( ContinuousOn.div ( continuousOn_const.mul ( continuousOn_pow 2 ) ) ( continuousOn_const.add ( continuousOn_const.mul continuousOn_id ) ) fun x hx => by linarith [ hx.1 ] ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( by norm_num [ add_comm, mul_comm, show x + 1 ≠ 0 from by linarith [ hx.1 ], show x * 2 + 6 ≠ 0 from by linarith [ hx.1 ] ] ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; nlinarith [ h_deriv c hc₁, mul_div_cancel₀ ( ( 1 + u ) * Real.log ( 1 + u ) - u - 3 * u ^ 2 / ( 6 + 2 * u ) ) ( by linarith : u ≠ 0 ) ] );
        convert h_ineq ( t * R / sigma_sq ) ( by positivity ) using 1 ; ring;
      field_simp at *;
      rw [ Real.exp_log ( by positivity ) ] ; nlinarith [ mul_pos ht hR, mul_div_cancel₀ ( sigma_sq + t * R ) hσ' ] ;

/-! ### Hoeffding private helpers -/

/-- **Matrix Laplace master bound** for Hoeffding.

For any `θ > 0`, the probability is bounded by
`2 d · exp(−θ t + θ² σ² / 2)`. This uses the Hoeffding-type
per-summand CGF bound.

**Status: sorry.** Same infrastructure requirements as Bernstein. -/
private lemma hoeffding_master_bound
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
    (t : ℝ) (ht : 0 < t)
    (θ : ℝ) (hθ : 0 < θ) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        (2 * ↑d * Real.exp (-θ * t + θ ^ 2 * sigma_sq / 2)) := by
  sorry

/-
**Scalar optimisation** for the Hoeffding bound.

The choice `θ = t / (4 σ²)` (when `σ² > 0`) yields
`−θ t + θ² σ² / 2 ≤ −t² / (8 σ²)`. When `σ² = 0`, any `θ > 0`
gives `−θ t < 0 = −t²/(8 · 0)`.
-/
private lemma hoeffding_scalar_opt
    (t sigma_sq : ℝ) (ht : 0 < t) (hσ : 0 ≤ sigma_sq) :
    ∃ θ : ℝ, 0 < θ ∧
      -θ * t + θ ^ 2 * sigma_sq / 2 ≤
        -(t ^ 2) / (8 * sigma_sq) := by
  by_cases h : sigma_sq = 0;
  · exact ⟨ 1, by norm_num, by norm_num [ h ] ; nlinarith ⟩;
  · exact ⟨ t / ( 4 * sigma_sq ), by positivity, by nlinarith [ mul_div_cancel₀ t ( by positivity : ( 4 * sigma_sq ) ≠ 0 ), mul_div_cancel₀ ( -t ^ 2 ) ( by positivity : ( 8 * sigma_sq ) ≠ 0 ), mul_self_pos.2 h ] ⟩

/-! ### Chernoff private helpers -/

/-- **Matrix Laplace master bound** for Chernoff (PSD summands).

For any `θ > 0`, the probability is bounded by
`d · exp(−θ t + μ_max · (eᶿᴿ − 1) / R)`. For PSD summands only the
upper tail is needed, hence factor `d` rather than `2d`.

**Status: sorry.** Same infrastructure requirements. -/
private lemma chernoff_master_bound
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
    (t : ℝ) (ht : mu_max ≤ t)
    (θ : ℝ) (hθ : 0 < θ) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        (↑d * Real.exp (-θ * t + mu_max * (Real.exp (θ * R) - 1) / R)) := by
  sorry

/-
Elementary inequality: `(1 + u) log(1 + u) − u ≥ 3 u² / (6 + 2u)` for `u ≥ 0`.
This is the key scalar bound used in Tropp's sub-Bernstein relaxation
of both the Bernstein and Chernoff matrix concentration bounds.
-/
private lemma phi_ge_sq_div (u : ℝ) (hu : 0 ≤ u) :
    (1 + u) * Real.log (1 + u) - u ≥ 3 * u ^ 2 / (6 + 2 * u) := by
  -- Let's define the function $f(u) = (1 + u) \log(1 + u) - u - \frac{3u^2}{6 + 2u}$ and show that $f(u) \geq 0$ for $u \geq 0$.
  set f : ℝ → ℝ := fun u => (1 + u) * Real.log (1 + u) - u - 3 * u^2 / (6 + 2 * u);
  -- We'll use the fact that $f(u)$ is differentiable and that its derivative is non-negative for $u \geq 0$.
  have h_deriv_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ deriv f u := by
    simp +zetaDelta at *;
    intro u hu; norm_num [ add_comm, mul_comm, show u + 1 ≠ 0 from by linarith, show u * 2 + 6 ≠ 0 from by linarith ];
    -- We'll use the fact that $Real.log (u + 1) \geq \frac{2u}{u + 2}$ for $u \geq 0$.
    have h_log_ineq : ∀ u : ℝ, 0 ≤ u → Real.log (u + 1) ≥ 2 * u / (u + 2) := by
      -- Let's choose any $u \geq 0$ and derive the inequality.
      intro u hu
      have h_deriv_nonneg : ∀ u : ℝ, 0 ≤ u → deriv (fun u => Real.log (u + 1) - 2 * u / (u + 2)) u ≥ 0 := by
        intro u hu; norm_num [ mul_comm, show u + 1 ≠ 0 by linarith, show u + 2 ≠ 0 by linarith ];
        rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> nlinarith;
      by_contra h_contra;
      have := exists_deriv_eq_slope ( f := fun u => Real.log ( u + 1 ) - 2 * u / ( u + 2 ) ) ( show u > 0 from hu.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at this;
      exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.log ( continuousAt_id.add continuousAt_const ) ( by linarith [ hx.1 ] ) ) ( ContinuousAt.div ( continuousAt_const.mul continuousAt_id ) ( continuousAt_id.add continuousAt_const ) ( by linarith [ hx.1 ] ) ) ) ( by exact fun x hx => by exact DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.add_const _ ) ( by linarith [ hx.1 ] ) ) ( DifferentiableAt.div ( differentiableAt_id.const_mul _ ) ( differentiableAt_id.add_const _ ) ( by linarith [ hx.1 ] ) ) ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; nlinarith [ h_deriv_nonneg c ( by linarith ), mul_div_cancel₀ ( Real.log ( u + 1 ) - 2 * u / ( u + 2 ) ) ( by linarith : u ≠ 0 ) ] );
    exact le_trans ( by rw [ div_le_div_iff₀ ] <;> nlinarith ) ( h_log_ineq u hu );
  by_contra h_contra;
  have := exists_deriv_eq_slope f ( show u > 0 from hu.lt_of_ne ( by rintro rfl; norm_num at h_contra ) );
  simp +zetaDelta at *;
  contrapose! this;
  exact ⟨ ContinuousOn.sub ( ContinuousOn.sub ( ContinuousOn.mul ( continuousOn_const.add continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ hx.1 ] ) ) continuousOn_id ) ( ContinuousOn.div ( continuousOn_const.mul ( continuousOn_pow 2 ) ) ( continuousOn_const.add ( continuousOn_const.mul continuousOn_id ) ) fun x hx => by linarith [ hx.1 ] ), fun x hx => DifferentiableAt.differentiableWithinAt ( by norm_num [ add_comm, mul_comm, show x + 1 ≠ 0 from by linarith [ hx.1 ], show x * 2 + 6 ≠ 0 from by linarith [ hx.1 ] ] ), fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_nonneg c hc.1.le ] ⟩

/-- **Scalar optimisation** for the Chernoff bound.

There exists `θ > 0` such that
`−θ t + μ_max · (eᶿᴿ − 1) / R ≤ −(t − μ_max)² / (2 μ_max + 2 R (t − μ_max) / 3)`.

Uses `phi_ge_sq_div` with `u = (t − μ_max) / μ_max` and `θ = log(t/μ_max)/R`. -/
private lemma chernoff_scalar_opt
    (t R mu_max : ℝ) (ht : mu_max < t) (hR : 0 < R)
    (hμ : 0 < mu_max) :
    ∃ θ : ℝ, 0 < θ ∧
      -θ * t + mu_max * (Real.exp (θ * R) - 1) / R ≤
        -((t - mu_max) ^ 2) / (2 * R * mu_max + 2 * R * (t - mu_max) / 3) := by
  sorry

/-! ## Main theorems -/

/-
**NOTE (correction from original):** The original statement had
exponent `−t² / (σ² + R t / 3)`, which is strictly stronger than the
actual Tropp (2012) bound and is **false** — a Rademacher
counterexample (d = 1, n = 1, X = ±I, R = 1, σ² = 1, t = 1) gives
P(‖X‖ ≥ 1) = 1 > 2 exp(−3/4) ≈ 0.945.

The correct Tropp bound has exponent `−t² / (2σ² + 2Rt/3)`. The
corrected statement below uses `2 * sigma_sq + 2 * R * t / 3` in the
denominator.
-/

/-- **Tropp's matrix Bernstein inequality** (Tropp 2012, Theorem 6.1.1;
Tropp 2015, Theorem 1.6.2; standard form).

Given independent self-adjoint random matrices `X₁, …, X_n` in
`Matrix (Fin d) (Fin d) ℝ` with

* `E[X_k] = 0`,
* `‖X_k‖_op ≤ R` almost surely, and
* matrix variance `σ² := ‖∑ E[X_k²]‖_op`,

then for all `t > 0`:
$$ ℙ(‖∑ X_k‖_op ≥ t) ≤ 2 d · \exp\!\bigl(−t^2 / (2 σ^2 + 2 R t / 3)\bigr). $$

**Proof structure:** Follows from `bernstein_master_bound` (matrix
Laplace transform parameterised by θ) and `bernstein_scalar_opt`
(optimal θ choice). -/
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
        (2 * ↑d * Real.exp (-(t ^ 2) / (2 * sigma_sq + 2 * R * t / 3))) := by
  obtain ⟨θ, hθ, hopt⟩ := bernstein_scalar_opt t R sigma_sq ht hR_pos hsigma_sq_nonneg
  exact le_trans
    (bernstein_master_bound n X R sigma_sq hR_pos hsigma_sq_nonneg
      h_indep h_sa h_zero_mean h_op_bound h_var_bound t ht θ hθ)
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hopt) (by positivity)))

/-- **Tropp's matrix Hoeffding inequality** (Tropp 2012, Theorem 1.3). -/
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
        (2 * ↑d * Real.exp (-(t ^ 2) / (8 * sigma_sq))) := by
  obtain ⟨θ, hθ, hopt⟩ := hoeffding_scalar_opt t sigma_sq ht hsigma_sq_nonneg
  exact le_trans
    (hoeffding_master_bound n X A sigma_sq hsigma_sq_nonneg
      h_indep h_sa h_A_sa h_zero_mean h_sq_bound h_var_bound t ht θ hθ)
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hopt) (by positivity)))

/-
**Tropp's matrix Chernoff inequality** (Tropp 2012, Theorem 1.1;
upper-tail form).
-/
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
        (↑d * Real.exp (-((t - mu_max) ^ 2) / (2 * R * mu_max + 2 * R * (t - mu_max) / 3))) := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · -- Case t = mu_max: the bound is d · exp(0) = d, and we use
    -- measure_le_one for d ≥ 1, empty-matrix triviality for d = 0.
    simp only [sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, neg_zero,
      zero_div, Real.exp_zero, mul_one]
    by_cases hd : d = 0;
    · subst hd; simp +decide;
      convert MeasureTheory.measure_empty;
      · ext ω; simp +decide [ Norm.norm ] ;
        convert hmu_max_pos using 1;
      · infer_instance;
    · exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simpa using ENNReal.ofReal_le_ofReal ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hd ) ) )
  · -- Case t > mu_max: use the master bound + scalar optimisation.
    obtain ⟨θ, hθ, hopt⟩ := chernoff_scalar_opt t R mu_max ht' hR_pos hmu_max_pos
    exact le_trans
      (chernoff_master_bound n X R mu_max hR_pos hmu_max_pos
        h_indep h_psd h_op_bound h_mean_bound t (le_of_lt ht') θ hθ)
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hopt) (by positivity)))

end Pythia