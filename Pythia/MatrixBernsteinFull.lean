import Mathlib
import Pythia.Basic

/-!
# Tropp's Matrix Bernstein Inequality — Full Proof Module

Reference: Joel A. Tropp (2012). *User-friendly tail bounds for sums of
random matrices*. Found. Comput. Math. 12:389–434, Theorem 6.1.1.

## Statement

For independent random Hermitian matrices `X_k` of dimension `d` with
`E[X_k] = 0`, `‖X_k‖ ≤ R` a.s., and variance parameter
`σ² ≥ ‖∑_k E[X_k²]‖`, the maximum eigenvalue of the sum satisfies:

  `P{λ_max(∑ X_k) ≥ t} ≤ d · exp(−t²/2 / (σ² + Rt/3))`

for all `t > 0`.

## Proof architecture

The proof follows Tropp's five-step strategy:

1. **Transfer to trace-exp** (matrix Laplace / Markov): for any `θ > 0`,
   `P(λ_max(S) ≥ t) ≤ e^{-θt} · E[tr(exp(θ S))]`.

2. **Lieb–Tropp master inequality**: for independent summands,
   `E[tr exp(θ S)] ≤ tr exp(∑_k log E[exp(θ X_k)])`.
   Requires **Lieb's concavity theorem** (Lieb 1973).

3. **Per-summand CGF bound** (Tropp 2012, Lemma 6.7):
   for zero-mean X with `λ_max(X) ≤ R`,
   `E[exp(θ X)] ⪯ I + (e^{θR} − θR − 1)/R² · E[X²]`.

4. **Trace bound assembly**: combining (2) and (3) yields
   `P(λ_max(S) ≥ t) ≤ d · exp(−θt + σ²/R² · (e^{θR} − θR − 1))`.

5. **Scalar optimization**: choose `θ* = log(1+Rt/σ²)/R` and use
   the elementary inequality `(1+x)log(1+x) − x ≥ x²/(2+2x/3)`
   to get the final Bernstein exponent `−t²/(2σ² + 2Rt/3)`.

Steps 1–4 are captured by the sorry-bridged `matrix_bernstein_laplace_step`.
Step 5 is proved in full. The main theorem assembles these components.

## Dependency note

Closure of `matrix_bernstein_laplace_step` requires:
- Lieb's concavity theorem (`Pythia.MatrixLieb` — parallel submission)
- Matrix CGF bound (Tropp 2012, Lemma 6.7)
- Functional calculus on Hermitian matrices
See `Pythia/MatrixBernstein.lean` for the detailed 5-step roadmap.
-/

namespace Pythia.MatrixBernsteinFull

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix BigOperators

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace

local instance borelMatrix (d : ℕ) :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  borel _

variable {d : ℕ}

/-! ## Section 1: Scalar analysis — the Bernstein function

The key scalar inequality behind the matrix Bernstein bound is:

  `ψ(x) ≥ x² / (2 + 2x/3)` for `x ≥ 0`

where `ψ(x) = (1+x) log(1+x) − x` is the Bernstein function.

This is proved by showing that `f(x) = (2+2x/3)·ψ(x) − x²` satisfies
`f(0) = f'(0) = f''(0) = 0` and `f'''(x) ≥ 0` for `x ≥ 0`.
-/

/-- The Bernstein function `ψ(x) = (1+x)log(1+x) − x`. -/
def psi (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - x

/-
The Bernstein function is nonneg for `x ≥ 0`.
-/
lemma psi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psi x := by
  exact sub_nonneg_of_le ( by nlinarith [ Real.log_inv ( 1 + x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 + x ) ), mul_inv_cancel₀ ( by linarith : ( 1 + x ) ≠ 0 ) ] )

/-
**Bernstein function bound**: `ψ(x) ≥ x² / (2 + 2x/3)` for `x ≥ 0`.

Proof sketch: let `f(x) = (2+2x/3)·ψ(x) − x²`. Then `f(0) = f'(0) = f''(0) = 0`
and `f'''(x) = (4/3)·x/(1+x)² ≥ 0`, so `f ≥ 0`.
-/
lemma psi_ge_bernstein_bound {x : ℝ} (hx : 0 ≤ x) :
    psi x ≥ x ^ 2 / (2 + 2 * x / 3) := by
  -- Since $g'(x) \leq 0$, we have $g(x) \leq g(0) = 0$ for $x \geq 0$.
  have h_g_nonpos : ∀ x ≥ 0, (1 + x) * Real.log (1 + x) - x - x ^ 2 / (2 + 2 * x / 3) ≥ 0 := by
    -- Let's simplify the expression for the derivative further by combining like terms.
    have h_deriv_simplified : ∀ x ≥ 0, deriv (fun x => (1 + x) * Real.log (1 + x) - x - x ^ 2 / (2 + 2 * x / 3)) x ≥ 0 := by
      intro x hx; norm_num [ add_comm, mul_comm, show x + 1 ≠ 0 from by linarith, show ( 2 + x * 2 / 3 ) ≠ 0 from by linarith ];
      -- We'll use the fact that $Real.log (1 + x) \geq \frac{2x}{2 + x}$ for $x \geq 0$.
      have h_log_ineq : ∀ x ≥ 0, Real.log (1 + x) ≥ 2 * x / (2 + x) := by
        -- Let's choose any $x \geq 0$ and simplify the expression for the derivative.
        intro x hx
        have h_deriv_nonneg : ∀ x > 0, deriv (fun x => Real.log (1 + x) - 2 * x / (2 + x)) x ≥ 0 := by
          intro x hx; norm_num [ add_comm, mul_comm, ne_of_gt, add_pos, hx ];
          rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> nlinarith;
        by_contra h_contra;
        have := exists_deriv_eq_slope ( f := fun x => Real.log ( 1 + x ) - 2 * x / ( 2 + x ) ) ( show x > 0 from hx.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at this;
        exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun y hy => by exact ContinuousAt.sub ( ContinuousAt.log ( continuousAt_const.add continuousAt_id ) ( by linarith [ hy.1 ] ) ) ( ContinuousAt.div ( continuousAt_const.mul continuousAt_id ) ( continuousAt_const.add continuousAt_id ) ( by linarith [ hy.1 ] ) ) ) ( by exact fun y hy => by exact DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.const_add _ ) ( by linarith [ hy.1 ] ) ) ( DifferentiableAt.div ( differentiableAt_id.const_mul _ ) ( differentiableAt_id.const_add _ ) ( by linarith [ hy.1 ] ) ) ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; nlinarith [ h_deriv_nonneg c hc₁, mul_div_cancel₀ ( Real.log ( 1 + x ) - 2 * x / ( 2 + x ) ) ( by linarith : x ≠ 0 ) ] );
      have := h_log_ineq x hx; rw [ ge_iff_le ] at this; rw [ div_le_iff₀ ] at * <;> ring_nf at * <;> nlinarith [ inv_mul_cancel₀ ( by linarith : ( 1 + x ) ≠ 0 ) ] ;
    intro x hx;
    by_contra h_contra;
    have := exists_deriv_eq_slope ( f := fun x => ( 1 + x ) * Real.log ( 1 + x ) - x - x ^ 2 / ( 2 + 2 * x / 3 ) ) ( show x > 0 from hx.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at this;
    apply_mod_cast absurd ( this _ _ ) _;
    · exact continuousOn_of_forall_continuousAt fun y hy => by exact ContinuousAt.sub ( ContinuousAt.sub ( ContinuousAt.mul ( continuousAt_const.add continuousAt_id ) ( ContinuousAt.log ( continuousAt_const.add continuousAt_id ) ( by linarith [ hy.1 ] ) ) ) continuousAt_id ) ( ContinuousAt.div ( continuousAt_id.pow 2 ) ( continuousAt_const.add ( continuousAt_const.mul continuousAt_id |> ContinuousAt.div_const <| 3 ) ) ( by linarith [ hy.1 ] ) ) ;
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.sub ( DifferentiableAt.mul ( differentiableAt_id.const_add _ ) ( DifferentiableAt.log ( differentiableAt_id.const_add _ ) ( by linarith [ hx.1 ] ) ) ) ( differentiableAt_id ) ) ( DifferentiableAt.div ( differentiableAt_id.pow 2 ) ( by norm_num [ mul_comm ] ) ( by linarith [ hx.1 ] ) ) );
    · exact fun ⟨ c, hc₁, hc₂ ⟩ => by nlinarith [ h_deriv_simplified c hc₁.1.le, mul_div_cancel₀ ( ( 1 + x ) * Real.log ( 1 + x ) - x - x ^ 2 / ( 2 + 2 * x / 3 ) ) ( by linarith : x ≠ 0 ) ] ;
  exact le_of_sub_nonneg ( h_g_nonpos x hx )

/-
The optimal Laplace parameter `θ* = log(1 + Rt/σ²) / R` is positive.
-/
lemma optimal_theta_pos' {R sigma_sq t : ℝ}
    (hR : 0 < R) (hsigma : 0 < sigma_sq) (ht : 0 < t) :
    0 < Real.log (1 + R * t / sigma_sq) / R := by
  exact div_pos ( Real.log_pos ( by rw [ lt_add_iff_pos_right ] ; positivity ) ) hR

/-
**Scalar Bernstein evaluation**: at `θ = log(1+Rt/σ²)/R`,
`−θt + σ²/R² · (e^{θR} − θR − 1) = −σ²/R² · ψ(Rt/σ²)`.

This is a direct algebraic identity using `e^{log(1+x)} = 1+x`.
-/
lemma scalar_bernstein_eval
    (R sigma_sq t : ℝ)
    (hR : 0 < R) (hsigma : 0 < sigma_sq) (ht : 0 < t) :
    -(Real.log (1 + R * t / sigma_sq) / R) * t +
      sigma_sq / R ^ 2 *
      (Real.exp (Real.log (1 + R * t / sigma_sq) / R * R) -
        Real.log (1 + R * t / sigma_sq) / R * R - 1) =
    -(sigma_sq / R ^ 2 * psi (R * t / sigma_sq)) := by
  rw [ div_mul_cancel₀ _ hR.ne' ]
  rw [ Real.exp_log ( by positivity ) ] ; unfold psi ; ring;
  grind

/-
**Scalar Bernstein optimization**: there exists `θ > 0` such that
`−θt + σ²/R²·(e^{θR} − θR − 1) ≤ −t²/(2σ² + 2Rt/3)`.

Combines `scalar_bernstein_eval` with `psi_ge_bernstein_bound`.
-/
lemma scalar_bernstein_optimization
    (R sigma_sq t : ℝ)
    (hR : 0 < R) (hsigma : 0 < sigma_sq) (ht : 0 < t) :
    ∃ theta : ℝ, 0 < theta ∧
      -theta * t + sigma_sq / R ^ 2 *
        (Real.exp (theta * R) - theta * R - 1) ≤
      -(t ^ 2 / (2 * sigma_sq + 2 / 3 * R * t)) := by
  refine' ⟨ Real.log ( 1 + R * t / sigma_sq ) / R, _, _ ⟩;
  · exact div_pos ( Real.log_pos ( by rw [ lt_add_iff_pos_right ] ; positivity ) ) hR;
  · rw [ scalar_bernstein_eval ];
    · refine' neg_le_neg _;
      convert mul_le_mul_of_nonneg_left ( psi_ge_bernstein_bound <| show 0 ≤ R * t / sigma_sq by positivity ) ( show 0 ≤ sigma_sq / R ^ 2 by positivity ) using 1 ; ring;
      field_simp
      ring
    · exact RCLike.ofReal_pos.mp hR
    · bv_omega
    · exact RCLike.ofReal_pos.mp ht

/-! ## Section 2: Sorry-bridged matrix infrastructure

The following lemma captures the full matrix-analytic content of
Tropp's proof (steps 1–4 of the roadmap). Closure requires:

1. **Lieb–Tropp master inequality** (Tropp 2012, Corollary 3.5):
   `E[tr exp(θ·∑X_k)] ≤ tr exp(∑ log E[exp(θ·X_k)])`

2. **Matrix CGF bound** (Tropp 2012, Lemma 6.7):
   `E[exp(θ·X_k)] ⪯ I + (e^{θR}-θR-1)/R² · E[X_k²]`

3. **Matrix Markov / Laplace**: `P(λ_max(S) ≥ t) ≤ e^{-θt}·E[tr exp(θS)]`

4. **Trace monotonicity**: `A ⪯ B ⟹ tr exp(A) ≤ tr exp(B)`
-/

/-- **Combined matrix Laplace–MGF bound** (Tropp 2012, §6.1 core).

For independent zero-mean Hermitian random matrices with operator-norm
bound `R` and matrix variance `σ²`, for any `θ > 0`:

  `P(‖∑ X_k‖ ≥ t) ≤ d · exp(−θt + σ²/R² · (e^{θR} − θR − 1))`

**Bridge**: closure reduces to Lieb concavity (`MatrixLieb`).

Note: this uses the exact CGF function `(e^u-u-1)`, not the weaker
bound `1/(2(1-u/3))`, so no constraint on `θR < 3` is needed. -/
lemma matrix_bernstein_laplace_step
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
    (R sigma_sq : ℝ)
    (hR_pos : 0 < R) (hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_sa : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (h_zero_mean : ∀ k i j, ∫ ω, (X k ω) i j ∂μ = 0)
    (h_op_bound : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ R)
    (h_var : ‖(Finset.univ : Finset (Fin n)).sum
        (fun k => fun i j => ∫ ω, ((X k ω) * (X k ω)) i j ∂μ)‖ ≤ sigma_sq)
    (theta : ℝ) (htheta : 0 < theta)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        ((d : ℝ) * Real.exp (-theta * t +
          sigma_sq / R ^ 2 *
            (Real.exp (theta * R) - theta * R - 1))) := by
  sorry

/-! ## Section 3: Main theorem — assembly from bridge + scalar optimization -/

/-- **Tropp's matrix Bernstein inequality** (Tropp 2012, Theorem 6.1.1).

For independent self-adjoint random matrices `X₁, …, X_n` in
`Matrix (Fin d) (Fin d) ℝ` with `E[X_k] = 0`, `‖X_k‖ ≤ R` a.s.,
and matrix variance `σ² ≥ ‖∑ E[X_k²]‖`, for all `t > 0`:

  `P{‖∑ X_k‖ ≥ t} ≤ d · exp(−t² / (2σ² + 2Rt/3))`

equivalently: `d · exp(−t²/2 / (σ² + Rt/3))`.

**Proof**: Choose the optimal Laplace parameter `θ* = log(1+Rt/σ²)/R`
in the sorry-bridged `matrix_bernstein_laplace_step`, then apply
`scalar_bernstein_optimization` to bound the exponent.
-/
theorem matrix_bernstein
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
    (R sigma_sq : ℝ)
    (hR_pos : 0 < R) (hsigma_sq_pos : 0 < sigma_sq)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_sa : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (h_zero_mean : ∀ k i j, ∫ ω, (X k ω) i j ∂μ = 0)
    (h_op_bound : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ R)
    (h_var : ‖(Finset.univ : Finset (Fin n)).sum
        (fun k => fun i j => ∫ ω, ((X k ω) * (X k ω)) i j ∂μ)‖ ≤ sigma_sq)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        ((d : ℝ) * Real.exp (-(t ^ 2 / (2 * sigma_sq + 2 / 3 * R * t)))) := by
  -- Get optimal θ from scalar_bernstein_optimization
  obtain ⟨theta, htheta_pos, h_scalar⟩ :=
    scalar_bernstein_optimization R sigma_sq t hR_pos hsigma_sq_pos ht
  -- Apply the matrix Laplace–MGF bridge at θ
  have h_laplace := matrix_bernstein_laplace_step n X R sigma_sq hR_pos
    (le_of_lt hsigma_sq_pos) h_indep h_sa h_zero_mean h_op_bound h_var
    theta htheta_pos t ht
  -- Chain: probability ≤ bridge bound ≤ Bernstein bound
  apply le_trans h_laplace
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ d)
  apply Real.exp_le_exp_of_le
  linarith

/-! ## Section 4: Two-sided corollary -/

/-- **Two-sided matrix Bernstein** (Tropp 2012, Theorem 6.1.1, symmetric).

`P(‖∑ X_k‖ ≥ t) ≤ 2d · exp(−t²/2 / (σ² + Rt/3))` -/
theorem matrix_bernstein_two_sided
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
    (R sigma_sq : ℝ)
    (hR_pos : 0 < R) (hsigma_sq_pos : 0 < sigma_sq)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_sa : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (h_zero_mean : ∀ k i j, ∫ ω, (X k ω) i j ∂μ = 0)
    (h_op_bound : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ R)
    (h_var : ‖(Finset.univ : Finset (Fin n)).sum
        (fun k => fun i j => ∫ ω, ((X k ω) * (X k ω)) i j ∂μ)‖ ≤ sigma_sq)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t} ≤
      ENNReal.ofReal
        (2 * (d : ℝ) * Real.exp (-(t ^ 2 / (2 * sigma_sq + 2 / 3 * R * t)))) := by
  calc μ {ω | ‖(Finset.univ : Finset (Fin n)).sum (fun k => X k ω)‖ ≥ t}
      ≤ ENNReal.ofReal
          ((d : ℝ) * Real.exp (-(t ^ 2 / (2 * sigma_sq + 2 / 3 * R * t)))) :=
        matrix_bernstein n X R sigma_sq hR_pos hsigma_sq_pos h_indep h_sa
          h_zero_mean h_op_bound h_var t ht
    _ ≤ ENNReal.ofReal
          (2 * (d : ℝ) * Real.exp (-(t ^ 2 / (2 * sigma_sq + 2 / 3 * R * t)))) := by
        apply ENNReal.ofReal_le_ofReal
        have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg' d
        have hexp := Real.exp_nonneg (-(t ^ 2 / (2 * sigma_sq + 2 / 3 * R * t)))
        nlinarith

end

end Pythia.MatrixBernsteinFull