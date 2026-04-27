/-
Pythia.Bennett — Bennett's inequality for iid bounded centered random variables.

# Main result

`bennett_iid`: For iid `X_i` with `|X_i| ≤ b` a.s., `E[X_i] = 0`,
`E[X_i²] ≤ σ²`, and `n ≥ 1` samples:

    P(∑_{i<n} X_i ≥ ε) ≤ exp(-(n σ² / b²) · ψ(b ε / (n σ²)))

where `ψ(u) = (1+u) log(1+u) − u` is the Bennett function.

# Proof strategy

1. **Pointwise Taylor bound** (`exp_le_bennett_pointwise`):
   For `|x| ≤ b`, `λ ≥ 0`, `b > 0`:
     `exp(λx) ≤ 1 + λx + (x/b)² · (exp(λb) − 1 − λb)`.

2. **Bennett MGF bound** (`bennett_mgf_bound`):
   Integrate the pointwise bound using `E[X] = 0` and `E[X²] ≤ σ²`:
     `mgf X μ λ ≤ exp(σ²/b² · (exp(λb) − 1 − λb))`.

3. **Chernoff + independence** (`bennett_tail_general_lambda`):
   Apply Markov to `exp(λ · ∑ X_i)`, factor by `iIndepFun.mgf_sum`,
   bound each factor with (2):
     `μ {S_n ≥ ε} ≤ exp(n σ²/b² · (exp(λb) − 1 − λb) − λε)`.

4. **Optimize** (`bennett_iid`):
   Set `λ = log(1 + b ε/(n σ²)) / b` and verify the exponent
   equals `−(n σ²/b²) · ψ(b ε/(n σ²))`.

Reference: Bennett (1962), Boucheron–Lugosi–Massart §2.7.
-/

import Mathlib
import Pythia.Basic
import Pythia.MGFBoundedSubGamma

namespace Pythia

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

/-! ## The Bennett function ψ -/

/-- The Bennett function `ψ(u) = (1+u) log(1+u) − u`.
Key property: `ψ(u) ≥ u²/(2(1 + u/3))` recovers Bernstein. -/
noncomputable def bennettPsi (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

lemma bennettPsi_zero : bennettPsi 0 = 0 := by
  simp [bennettPsi, Real.log_one]

lemma bennettPsi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bennettPsi u := by
  exact sub_nonneg_of_le ( by nlinarith [ Real.log_inv ( 1 + u ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 + u ) ), mul_inv_cancel₀ ( by linarith : ( 1 + u ) ≠ 0 ) ] )

/-! ## Pointwise exponential bound -/

/-
**Pointwise Bennett bound.** For `|x| ≤ b`, `λ ≥ 0`, `b > 0`:
  `exp(λx) ≤ 1 + λx + (x/b)² · (exp(λb) − 1 − λb)`.

Proof sketch: let `h(x) = 1 + λx + (x/b)²·(exp(λb)−1−λb) − exp(λx)`.
Then `h(0) = 0`, `h(b) = 0`. On `[−b, 0]`, `h` is convex with
`h'(0) = 0`, hence `h ≥ 0`. On `[0, b]`, `h` has `h(0) = 0`,
`h'(0) = 0`, `h(b) = 0`, and `h''` is decreasing (so `h` is first
convex then concave), giving `h ≥ 0`.
-/
set_option maxHeartbeats 800000 in
lemma exp_le_bennett_pointwise {x b lam : ℝ}
    (hb : 0 < b) (hx : |x| ≤ b) (hlam : 0 ≤ lam) :
    Real.exp (lam * x) ≤
      1 + lam * x + (x / b) ^ 2 * (Real.exp (lam * b) - 1 - lam * b) := by
  by_cases hlam0 : lam = 0 <;> simp_all +decide [ abs_le ];
  -- Let $g(t) = \frac{\exp(t) - 1 - t}{t^2}$ which is increasing for $t \geq 0$.
  set g : ℝ → ℝ := fun t => if t = 0 then 1 / 2 else (Real.exp t - 1 - t) / t^2
  have hg_inc : ∀ t1 t2 : ℝ, 0 ≤ t1 → t1 ≤ t2 → g t1 ≤ g t2 := by
    -- We'll use the fact that $g(t)$ is increasing for $t \geq 0$.
    have hg_deriv_nonneg : ∀ t > 0, deriv g t ≥ 0 := by
      -- Let's calculate the derivative of $g(t)$ for $t > 0$.
      have hg_deriv : ∀ t > 0, deriv g t = (t * Real.exp t - 2 * Real.exp t + t + 2) / t^3 := by
        intro t ht; rw [ show deriv g t = deriv ( fun t => ( Real.exp t - 1 - t ) / t ^ 2 ) t by exact Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem ( Ioi_mem_nhds ht ) fun x hx => if_neg hx.out.ne' ] ; norm_num [ Real.differentiableAt_exp, ht.ne', mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv ] ; ring;
        -- Combine like terms and simplify the expression.
        field_simp
        ring;
      -- We'll use the fact that $t * \exp(t) - 2 * \exp(t) + t + 2 \geq 0$ for $t > 0$.
      have h_num_nonneg : ∀ t > 0, t * Real.exp t - 2 * Real.exp t + t + 2 ≥ 0 := by
        intro t ht
        have h_deriv_nonneg : ∀ t > 0, deriv (fun t => t * Real.exp t - 2 * Real.exp t + t + 2) t ≥ 0 := by
          norm_num [ Real.differentiableAt_exp ];
          exact fun t ht => by nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ] ;
        have := exists_deriv_eq_slope ( f := fun t => t * Real.exp t - 2 * Real.exp t + t + 2 ) ht; norm_num at *;
        exact this ( Continuous.continuousOn <| by continuity ) ( Differentiable.differentiableOn <| by norm_num [ Real.differentiable_exp ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by nlinarith [ h_deriv_nonneg c hc₁.1, mul_div_cancel₀ ( t * Real.exp t - 2 * Real.exp t + t + 2 ) ht.ne' ] ;
      exact fun t ht => hg_deriv t ht ▸ div_nonneg ( h_num_nonneg t ht ) ( pow_nonneg ht.le 3 );
    intro t1 t2 ht1 ht2; cases eq_or_lt_of_le ht1 <;> cases eq_or_lt_of_le ht2 <;> norm_num at *;
    · grind;
    · norm_num [ ← ‹0 = t1›, g ];
      rw [ if_neg ( by linarith ), le_div_iff₀ ] <;> try nlinarith;
      -- We'll use the fact that $e^t \geq 1 + t + \frac{t^2}{2}$ for all $t \geq 0$.
      have h_exp_bound : ∀ t : ℝ, 0 ≤ t → Real.exp t ≥ 1 + t + t^2 / 2 :=
        fun t a => Real.quadratic_le_exp_of_nonneg a;
      linarith [ h_exp_bound t2 ( by linarith ) ];
    · grind;
    · have := exists_deriv_eq_slope g ‹_›;
      contrapose! this;
      simp +zetaDelta at *;
      exact ⟨ ContinuousOn.congr ( show ContinuousOn ( fun t => ( Real.exp t - 1 - t ) / t ^ 2 ) ( Set.Icc t1 t2 ) from ContinuousOn.div ( ContinuousOn.sub ( ContinuousOn.sub ( Real.continuousOn_exp ) continuousOn_const ) continuousOn_id ) ( continuousOn_pow 2 ) fun x hx => by nlinarith [ hx.1 ] ) fun x hx => if_neg ( by linarith [ hx.1 ] ), fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.congr_of_eventuallyEq ( by exact DifferentiableAt.div ( by norm_num [ Real.differentiableAt_exp ] ) ( differentiableAt_pow 2 ) ( by nlinarith [ hx.1 ] ) ) ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hx.1 hx.2 ) fun y hy => if_neg ( by linarith [ hy.1 ] ) ) ), fun c hc1 hc2 => by rw [ eq_div_iff ] <;> nlinarith [ hg_deriv_nonneg c ( by linarith ) ] ⟩;
  -- Since $g$ is increasing, we have $g(lam * x) \leq g(lam * b)$.
  have hg_le : g (lam * x) ≤ g (lam * b) := by
    by_cases hlamx_nonneg : 0 ≤ lam * x;
    · exact hg_inc _ _ hlamx_nonneg ( mul_le_mul_of_nonneg_left hx.2 hlam );
    · -- Since $g$ is increasing, we have $g(lam * x) \leq g(0)$.
      have hg_le_zero : g (lam * x) ≤ g 0 := by
        have hg_le_zero : ∀ t : ℝ, t < 0 → g t ≤ g 0 := by
          intros t ht_neg
          have hg_le_zero : (Real.exp t - 1 - t) / t^2 ≤ 1 / 2 := by
            rw [ div_le_iff₀ ] <;> try nlinarith;
            have := exp_sub_one_sub_le_sq_nonpos ht_neg.le;
            linarith;
          aesop;
        exact hg_le_zero _ ( not_le.mp hlamx_nonneg );
      refine le_trans hg_le_zero ?_;
      exact hg_inc 0 ( lam * b ) le_rfl ( by nlinarith );
  simp +zetaDelta at *;
  split_ifs at hg_le <;> simp_all +decide [ ne_of_gt, division_def ];
  field_simp at hg_le ⊢;
  rw [ div_le_iff₀ ] at hg_le <;> first | positivity | linarith;

/-! ## Bennett MGF bound -/

/-
**Bennett MGF bound.** For `X` measurable with `|X| ≤ b` a.s.,
`E[X] = 0`, `E[X²] ≤ σ²`, and `λ ≥ 0`:

  `mgf X μ λ ≤ exp(σ²/b² · (exp(λb) − 1 − λb))`.

Proof: integrate `exp_le_bennett_pointwise`, using `E[X] = 0` to
kill the linear term and `E[X²] ≤ σ²` for the quadratic, then
apply `1 + x ≤ exp(x)`.
-/
set_option maxHeartbeats 400000 in
lemma bennett_mgf_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b σ_sq : ℝ}
    (hX_meas : Measurable X)
    (hb : 0 < b)
    (h_bounded : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h_centered : ∫ ω, X ω ∂μ = 0)
    (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ σ_sq)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    mgf X μ lam ≤
      Real.exp (σ_sq / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b)) := by
  refine' le_trans _ ( Real.add_one_le_exp _ );
  refine' le_trans ( MeasureTheory.integral_mono_ae _ _ _ ) _;
  refine' fun ω => 1 + lam * X ω + ( X ω / b ) ^ 2 * ( Real.exp ( lam * b ) - 1 - lam * b );
  · exact integrable_exp_mul_of_bounded hX_meas h_bounded;
  · apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.mul_const, MeasureTheory.Integrable.const_mul ] <;> norm_num;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      exacts [ fun _ => b, MeasureTheory.integrable_const _, hX_meas.aestronglyMeasurable, h_bounded ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun ω => ( b / b ) ^ 2;
      · norm_num;
      · exact MeasureTheory.AEStronglyMeasurable.pow ( hX_meas.aestronglyMeasurable.mul_const _ ) _;
      · filter_upwards [ h_bounded ] with ω hω using by simpa [ abs_div, abs_of_nonneg hb.le ] using pow_le_pow_left₀ ( by positivity ) ( div_le_div_of_nonneg_right ( hω ) hb.le ) 2;
  · filter_upwards [ h_bounded ] with ω hω using exp_le_bennett_pointwise hb hω hlam;
  · rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
    · simp +decide [ div_eq_inv_mul, mul_pow, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, h_centered ];
      nlinarith [ inv_pos.2 ( sq_pos_of_pos hb ), mul_le_mul_of_nonneg_left h_var ( inv_nonneg.2 ( sq_nonneg b ) ), Real.add_one_le_exp ( lam * b ), mul_nonneg hlam hb.le ];
    · norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      exacts [ fun _ => b, MeasureTheory.integrable_const _, hX_meas.aestronglyMeasurable, h_bounded ];
    · refine' MeasureTheory.Integrable.add _ _;
      · norm_num;
      · refine' MeasureTheory.Integrable.const_mul _ _;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun _ => b, MeasureTheory.integrable_const _, hX_meas.aestronglyMeasurable, h_bounded ];
    · refine' MeasureTheory.Integrable.mul_const _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun ω => ( b / b ) ^ 2;
      · norm_num;
      · exact MeasureTheory.AEStronglyMeasurable.pow ( hX_meas.aestronglyMeasurable.mul_const _ ) _;
      · filter_upwards [ h_bounded ] with ω hω using by simpa [ abs_div, abs_of_nonneg hb.le ] using pow_le_pow_left₀ ( by positivity ) ( div_le_div_of_nonneg_right hω hb.le ) 2;

/-! ## Chernoff bound for general λ -/

/-
Integrability of `exp(λ · S_n)` for bounded `X_i`.
-/
lemma integrable_exp_sum_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (n : ℕ) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * (∑ i ∈ range n, X i ω))) μ := by
  have h_bounded : ∀ᵐ ω ∂μ, |∑ i ∈ range n, X i ω| ≤ n * b := by
    filter_upwards [ MeasureTheory.ae_all_iff.2 h_bounded ] with ω hω using le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => hω _ ) ( by simp +decide ) );
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => Real.exp ( |lam| * ( n * b ) );
  · norm_num;
  · exact Measurable.aestronglyMeasurable ( by measurability );
  · filter_upwards [ h_bounded ] with ω hω using by simpa using Real.exp_le_exp.2 ( by cases abs_cases lam <;> nlinarith [ abs_le.mp hω ] ) ;

/-
**Chernoff bound with general λ.** For iid bounded centered RVs:

  `μ {S_n ≥ ε} ≤ exp(n · σ²/b² · (exp(λb) − 1 − λb) − λε)`.

Combines exponential Markov (`measure_ge_le_exp_mul_mgf`),
independence factoring (`iIndepFun.mgf_sum`), and the Bennett MGF
bound.
-/
lemma bennett_tail_general_lambda
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b σ_sq : ℝ}
    (hb : 0 < b) (hσ_sq : 0 < σ_sq)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_centered : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_var : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ σ_sq)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps)
    {lam : ℝ} (hlam : 0 < lam) :
    μ {ω | (range n).sum (fun i => X i ω) ≥ eps} ≤
      ENNReal.ofReal (Real.exp
        (↑n * σ_sq / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b) - lam * eps)) := by
  -- Apply the exponential Markov inequality to the sum S = ∑_{i ∈ range n} X i.
  have h_exp_markov : (μ {ω | ∑ i ∈ (range n), (X i ω) ≥ eps}) ≤ ENNReal.ofReal ((Real.exp (-lam * eps)) * (mgf (∑ i ∈ (range n), (X i)) μ lam)) := by
    have := @ProbabilityTheory.measure_ge_le_exp_mul_mgf;
    convert ENNReal.ofReal_le_ofReal ( this eps hlam.le _ ) using 1;
    · simp +decide [ MeasureTheory.measureReal_def ];
    · infer_instance;
    · convert integrable_exp_sum_of_bounded h_meas h_bounded n lam using 1;
      simp +decide [ Finset.sum_apply ];
  -- Use the independence factoring to bound the MGF.
  have h_mgf_bound : (mgf (∑ i ∈ (range n), (X i)) μ lam) ≤ (Real.exp (n * σ_sq / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b))) := by
    have h_mgf_bound : (mgf (∑ i ∈ (range n), (X i)) μ lam) = (∏ i ∈ (range n), (mgf (X i) μ lam)) := by
      exact iIndepFun.mgf_sum h_indep h_meas (range n);
    have h_mgf_bound : ∀ i, (mgf (X i) μ lam) ≤ (Real.exp (σ_sq / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b))) := by
      intro i;
      convert bennett_mgf_bound ( h_meas i ) hb ( h_bounded i ) ( h_centered i ) ( h_var i ) hlam.le using 1;
    convert Finset.prod_le_prod ?_ fun i ( hi : i ∈ Finset.range n ) => h_mgf_bound i <;> simp +decide [ *, mul_assoc, mul_div_assoc ];
    · rw [ ← Real.exp_nat_mul, mul_comm ];
    · exact fun i _ => MeasureTheory.integral_nonneg fun ω => Real.exp_nonneg _;
  convert h_exp_markov.trans ( ENNReal.ofReal_le_ofReal <| mul_le_mul_of_nonneg_left h_mgf_bound <| Real.exp_nonneg _ ) using 1 ; rw [ ← Real.exp_add ] ; ring

/-! ## Optimal λ and algebraic identity -/

/-
The exponent at optimal `λ = log(1 + u) / b` (where `u = bε/(nσ²)`)
equals `−(nσ²/b²) · ψ(u)`. Pure algebra.
-/
lemma bennett_exponent_optimal {b σ_sq eps : ℝ} {n : ℕ}
    (hb : 0 < b) (hσ_sq : 0 < σ_sq)
    (hn : 0 < n) (hε : 0 < eps) :
    let u := b * eps / (↑n * σ_sq)
    ↑n * σ_sq / b ^ 2 *
        (Real.exp (Real.log (1 + u) / b * b) - 1 - Real.log (1 + u) / b * b) -
      Real.log (1 + u) / b * eps =
    -(↑n * σ_sq / b ^ 2 * bennettPsi u) := by
  field_simp;
  rw [ Real.exp_log ( by positivity ) ];
  unfold bennettPsi; field_simp; ring;

/-
The optimal λ for Bennett is positive.
-/
lemma bennett_optimal_lam_pos {b σ_sq eps : ℝ} {n : ℕ}
    (hb : 0 < b) (hσ_sq : 0 < σ_sq)
    (hn : 0 < n) (hε : 0 < eps) :
    0 < Real.log (1 + b * eps / (↑n * σ_sq)) / b := by
  exact div_pos ( Real.log_pos ( by exact lt_add_of_pos_right _ ( by positivity ) ) ) hb

/-! ## Main theorem -/

/-
**Bennett's inequality** for iid bounded centered random variables.

For `X_i` iid with `|X_i| ≤ b` a.s., `E[X_i] = 0`, `E[X_i²] ≤ σ²`,
`n ≥ 1` samples, and `ε > 0`:

$$P\Bigl(\sum_{i=0}^{n-1} X_i \ge \varepsilon\Bigr)
  \le \exp\!\Bigl(-\frac{n\sigma^2}{b^2}\,
       \psi\!\Bigl(\frac{b\varepsilon}{n\sigma^2}\Bigr)\Bigr)$$

where $\psi(u) = (1+u)\log(1+u) - u$.

Proof: apply `bennett_tail_general_lambda` with the optimal
`λ = \log(1 + bε/(nσ²)) / b`, then use `bennett_exponent_optimal`
to simplify the exponent.
-/
theorem bennett_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b σ_sq : ℝ}
    (hb : 0 < b) (hσ_sq : 0 < σ_sq)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_centered : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_var : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ σ_sq)
    {n : ℕ} (hn : 0 < n) {eps : ℝ} (hε : 0 < eps) :
    μ {ω | (range n).sum (fun i => X i ω) ≥ eps} ≤
      ENNReal.ofReal (Real.exp
        (-(↑n * σ_sq / b ^ 2 * bennettPsi (b * eps / (↑n * σ_sq))))) := by
  convert bennett_tail_general_lambda hb hσ_sq h_meas h_indep h_bounded h_centered h_var n eps hε ( bennett_optimal_lam_pos hb hσ_sq hn hε ) using 1;
  rw [ bennett_exponent_optimal hb hσ_sq hn hε ]

end Pythia