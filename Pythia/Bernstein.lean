/-
Pythia.Bernstein — Bernstein's inequality + Bennett-Bernstein
maximal inequality for martingales.
-/
import Mathlib
import Pythia.Basic
import Pythia.SubGamma
import Pythia.MGFBoundedSubGamma
import Pythia.Tactic.Pythia

namespace Pythia

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Section 1 — Bernstein for sub-gamma martingales (CLOSED) -/

@[stat_lemma]
theorem bernstein_of_subGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {V b : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (M : SubGammaMG (V / N) (b / 3) 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * (V + b * τ / 3)))) := by
  have h := subGamma_ville_ineq (M := M) hM0 τ hτ N hN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h_denom_eq :
      (2 * (V / N) * N + 2 * (b / 3) * τ) = 2 * (V + b * τ / 3) := by
    field_simp
  have h_rate_eq :
      Real.exp (-(τ^2) / (2 * (V / N) * N + 2 * (b / 3) * τ))
        = Real.exp (-(τ^2) / (2 * (V + b * τ / 3))) := by
    rw [h_denom_eq]
  rw [h_rate_eq] at h
  exact h

/-! ## Section 2 — Helper lemmas -/

/-
Martingale increments have zero conditional mean.
-/
lemma martingale_increment_zero_condExp
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : Martingale M 𝓕 μ) (t : ℕ) :
    μ[fun ω => M (t + 1) ω - M t ω | 𝓕 t] =ᵐ[μ] 0 := by
  have := h_mart.2 t;
  have h_condExp_sub : μ[fun ω => M (t + 1) ω - M t ω | 𝓕 t] =ᵐ[μ] μ[fun ω => M (t + 1) ω | 𝓕 t] - μ[fun ω => M t ω | 𝓕 t] := by
    apply_rules [ MeasureTheory.condExp_sub ];
    · exact h_mart.integrable _;
    · exact h_mart.integrable _;
  filter_upwards [ h_condExp_sub, this ( t + 1 ) ( Nat.le_succ _ ), this t le_rfl ] with ω hω₁ hω₂ hω₃ using by aesop;

/-
Exponential integrability for bounded martingales starting at 0.
-/
lemma integrable_exp_of_bounded_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : Martingale M 𝓕 μ)
    {b : ℝ} (hb : 0 < b)
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |M (t + 1) ω - M t ω| ≤ b)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0)
    (t : ℕ) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * M t ω)) μ := by
  -- Since $|M_t| \leq t \cdot b$ almost surely, we have $|\lambda M_t| \leq |\lambda| \cdot t \cdot b$ almost surely.
  have h_abs : ∀ᵐ ω ∂μ, |lam * M t ω| ≤ |lam| * t * b := by
    have h_abs : ∀ᵐ ω ∂μ, |M t ω| ≤ t * b := by
      induction' t with t ih <;> simp_all +decide [ Nat.cast_succ, add_mul ];
      filter_upwards [ ih, h_bounded t ] with ω hω₁ hω₂ using abs_le.mpr ⟨ by linarith [ abs_le.mp hω₁, abs_le.mp hω₂ ], by linarith [ abs_le.mp hω₁, abs_le.mp hω₂ ] ⟩;
    filter_upwards [ h_abs ] with ω hω using by rw [ abs_mul, mul_assoc ] ; exact mul_le_mul_of_nonneg_left hω ( abs_nonneg lam ) ;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => Real.exp ( |lam| * t * b );
  · norm_num;
  · exact Real.continuous_exp.comp_aestronglyMeasurable ( h_mart.integrable t |> fun h => h.aestronglyMeasurable.const_mul _ );
  · filter_upwards [ h_abs ] with ω hω using by simpa using Real.exp_le_exp.2 ( le_of_abs_le hω ) ;

/-
Exponential integrability of bounded increment.
-/
lemma integrable_exp_increment_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : Martingale M 𝓕 μ)
    {b : ℝ}
    (h_bounded : ∀ᵐ ω ∂μ, |M (t + 1) ω - M t ω| ≤ b)
    (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * (M (t + 1) ω - M t ω))) μ := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => Real.exp ( |lam| * b );
  · norm_num;
  · have h_integrable : MeasureTheory.Integrable (fun ω => M (t + 1) ω - M t ω) μ := by
      exact MeasureTheory.Integrable.sub ( h_mart.integrable _ ) ( h_mart.integrable _ );
    exact Real.continuous_exp.comp_aestronglyMeasurable ( h_integrable.aestronglyMeasurable.const_mul _ );
  · filter_upwards [ h_bounded ] with ω hω using by simpa using Real.exp_le_exp.2 ( by cases abs_cases lam <;> nlinarith [ abs_le.mp hω ] ) ;

/-
Conditional MGF bound in the form matching `SubGammaMG.increments_subGamma`.
-/
lemma condExp_exp_le_subGamma_form
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {t : ℕ}
    {M : ℕ → Ω → ℝ} {b V : ℝ}
    (hb : 0 < b)
    (h_mart : Martingale M 𝓕 μ)
    (h_bounded : ∀ᵐ ω ∂μ, |M (t + 1) ω - M t ω| ≤ b)
    (h_var : ∀ᵐ ω ∂μ,
      (μ[fun ω' => (M (t + 1) ω' - M t ω')^2 | 𝓕 t]) ω ≤ V)
    {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam : b / 3 * lam < 1) :
    ∀ᵐ ω ∂μ,
      (μ[fun ω' => Real.exp (lam *
        (M (t + 1) ω' - M t ω')) | 𝓕 t]) ω ≤
      Real.exp (V * lam^2 / (2 * (1 - b / 3 * lam))) := by
  have h_condExp_mono : ∀ᵐ ω ∂μ, (μ[fun ω' => Real.exp (lam * (M (t + 1) ω' - M t ω')) | 𝓕 t]) ω ≤ (μ[fun ω' => 1 + lam * (M (t + 1) ω' - M t ω') + (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω := by
    apply_rules [ MeasureTheory.condExp_mono ];
    · apply_rules [ integrable_exp_increment_of_bounded ];
    · refine' MeasureTheory.Integrable.add _ _;
      · exact MeasureTheory.Integrable.add ( MeasureTheory.integrable_const _ ) ( MeasureTheory.Integrable.const_mul ( h_mart.integrable _ |> fun h => h.sub ( h_mart.integrable _ ) ) _ );
      · refine' MeasureTheory.Integrable.div_const _ _;
        have h_integrable : Integrable (fun ω' => (M (t + 1) ω' - M t ω')^2) μ := by
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun ω => b ^ 2;
          · norm_num;
          · have := h_mart.integrable ( t + 1 );
            simpa only [ sq ] using this.aestronglyMeasurable.sub ( h_mart.integrable t |> MeasureTheory.Integrable.aestronglyMeasurable ) |> fun h => h.mul h;
          · filter_upwards [ h_bounded ] with ω hω using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) hω 2;
        simpa only [ mul_pow ] using h_integrable.const_mul _;
    · filter_upwards [ h_bounded ] with ω hω;
      convert exp_mul_le_one_add_add_sq_div hb.le hω hlam_nn ( show b * lam < 3 by linarith ) using 1;
      ring;
  have h_condExp_add : ∀ᵐ ω ∂μ, (μ[fun ω' => 1 + lam * (M (t + 1) ω' - M t ω') + (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω = 1 + (μ[fun ω' => lam * (M (t + 1) ω' - M t ω') | 𝓕 t]) ω + (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω := by
    have h_condExp_add : ∀ᵐ ω ∂μ, (μ[fun ω' => 1 + lam * (M (t + 1) ω' - M t ω') + (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω = (μ[fun ω' => 1 | 𝓕 t]) ω + (μ[fun ω' => lam * (M (t + 1) ω' - M t ω') | 𝓕 t]) ω + (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω := by
      have h_condExp_add : Integrable (fun ω' => 1 : Ω → ℝ) μ ∧ Integrable (fun ω' => lam * (M (t + 1) ω' - M t ω')) μ ∧ Integrable (fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam))) μ := by
        have h_integrable : Integrable (fun ω' => (M (t + 1) ω' - M t ω') ^ 2) μ := by
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun ω => b ^ 2;
          · norm_num;
          · have := h_mart.integrable ( t + 1 );
            have := h_mart.integrable t;
            simpa only [ sq ] using ( ‹Integrable ( M ( t + 1 ) ) μ›.sub ‹Integrable ( M t ) μ› ).aestronglyMeasurable.mul ( ‹Integrable ( M ( t + 1 ) ) μ›.sub ‹Integrable ( M t ) μ› ).aestronglyMeasurable;
          · filter_upwards [ h_bounded ] with ω hω using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) hω 2;
        simp_all +decide [ mul_pow ];
        exact ⟨ by exact MeasureTheory.Integrable.const_mul ( h_mart.integrable _ |> fun h => h.sub ( h_mart.integrable _ ) ) _, by exact MeasureTheory.Integrable.div_const ( MeasureTheory.Integrable.const_mul h_integrable _ ) _ ⟩;
      have h_condExp_add : ∀ᵐ ω ∂μ, (μ[fun ω' => 1 + lam * (M (t + 1) ω' - M t ω') | 𝓕 t]) ω = (μ[fun ω' => 1 | 𝓕 t]) ω + (μ[fun ω' => lam * (M (t + 1) ω' - M t ω') | 𝓕 t]) ω := by
        apply_rules [ MeasureTheory.condExp_add ];
        · exact h_condExp_add.1;
        · exact h_condExp_add.2.1;
      have h_condExp_add : ∀ᵐ ω ∂μ, (μ[fun ω' => 1 + lam * (M (t + 1) ω' - M t ω') + (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω = (μ[fun ω' => 1 + lam * (M (t + 1) ω' - M t ω') | 𝓕 t]) ω + (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω := by
        apply_rules [ MeasureTheory.condExp_add ];
        · exact MeasureTheory.Integrable.add ( MeasureTheory.integrable_const _ ) ( by tauto );
        · tauto;
      filter_upwards [ h_condExp_add, ‹∀ᵐ ω ∂μ, μ[fun ω' => 1 + lam * (M (t + 1) ω' - M t ω') | 𝓕 t] ω = μ[fun ω' => 1 | 𝓕 t] ω + μ[fun ω' => lam * (M (t + 1) ω' - M t ω') | 𝓕 t] ω› ] with ω hω₁ hω₂ using by rw [ hω₁, hω₂ ] ;
    filter_upwards [ h_condExp_add ] with ω hω;
    rw [ hω, MeasureTheory.condExp_of_stronglyMeasurable ] <;> norm_num;
    exact stronglyMeasurable_const;
  have h_condExp_mul : ∀ᵐ ω ∂μ, (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω ≤ (lam ^ 2 * V) / (2 * (1 - b / 3 * lam)) := by
    have h_condExp_mul : ∀ᵐ ω ∂μ, (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 | 𝓕 t]) ω ≤ lam ^ 2 * V := by
      have h_condExp_mul : ∀ᵐ ω ∂μ, (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 | 𝓕 t]) ω = lam ^ 2 * (μ[fun ω' => (M (t + 1) ω' - M t ω') ^ 2 | 𝓕 t]) ω := by
        have h_condExp_mul : ∀ᵐ ω ∂μ, (μ[fun ω' => lam ^ 2 * (M (t + 1) ω' - M t ω') ^ 2 | 𝓕 t]) ω = lam ^ 2 * (μ[fun ω' => (M (t + 1) ω' - M t ω') ^ 2 | 𝓕 t]) ω := by
          apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
          · exact stronglyMeasurable_const;
          · refine' MeasureTheory.Integrable.const_mul _ _;
            refine' MeasureTheory.MemLp.integrable_sq _;
            refine' MemLp.mono' _ _ _;
            exact fun ω => b;
            · exact memLp_const _;
            · exact MeasureTheory.Integrable.aestronglyMeasurable ( h_mart.integrable _ |> fun h => h.sub ( h_mart.integrable _ ) );
            · exact h_bounded;
          · refine' MeasureTheory.MemLp.integrable_sq _;
            refine' MemLp.mono' _ _ _;
            exact fun ω => b;
            · exact memLp_const _;
            · exact MeasureTheory.Integrable.aestronglyMeasurable ( h_mart.integrable _ |> fun h => h.sub ( h_mart.integrable _ ) );
            · exact h_bounded;
        simpa only [ mul_pow ] using h_condExp_mul;
      filter_upwards [ h_condExp_mul, h_var ] with ω hω₁ hω₂ using by rw [ hω₁ ] ; exact mul_le_mul_of_nonneg_left hω₂ ( sq_nonneg _ ) ;
    have h_condExp_mul : ∀ᵐ ω ∂μ, (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 / (2 * (1 - b / 3 * lam)) | 𝓕 t]) ω = (μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 | 𝓕 t]) ω / (2 * (1 - b / 3 * lam)) := by
      convert MeasureTheory.condExp_mul_of_stronglyMeasurable_right _ _ _ using 1;
      · exact stronglyMeasurable_const;
      · refine' MeasureTheory.Integrable.mul_const _ _;
        have h_integrable : Integrable (fun ω' => (M (t + 1) ω' - M t ω') ^ 2) μ := by
          refine' MeasureTheory.Integrable.mono' _ _ _;
          use fun ω => b ^ 2;
          · norm_num;
          · have h_integrable : MeasureTheory.Integrable (fun ω' => M (t + 1) ω' - M t ω') μ := by
              exact MeasureTheory.Integrable.sub ( h_mart.integrable _ ) ( h_mart.integrable _ );
            simpa only [ sq ] using h_integrable.aestronglyMeasurable.mul h_integrable.aestronglyMeasurable;
          · filter_upwards [ h_bounded ] with ω hω using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) hω 2;
        convert h_integrable.const_mul ( lam ^ 2 ) using 2 ; ring;
      · have h_integrable : Integrable (fun ω' => (M (t + 1) ω' - M t ω') ^ 2) μ := by
          refine' MeasureTheory.Integrable.mono' _ _ _;
          use fun ω => b ^ 2;
          · norm_num;
          · have h_integrable : MeasureTheory.Integrable (fun ω' => M (t + 1) ω' - M t ω') μ := by
              exact MeasureTheory.Integrable.sub ( h_mart.integrable _ ) ( h_mart.integrable _ );
            simpa only [ sq ] using h_integrable.aestronglyMeasurable.mul h_integrable.aestronglyMeasurable;
          · filter_upwards [ h_bounded ] with ω hω using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) hω 2;
        convert h_integrable.const_mul ( lam ^ 2 ) using 2 ; ring;
    filter_upwards [ h_condExp_mul, ‹∀ᵐ ω ∂μ, μ[fun ω' => (lam * (M (t + 1) ω' - M t ω')) ^ 2 | 𝓕 t] ω ≤ lam ^ 2 * V› ] with ω hω₁ hω₂ using by rw [ hω₁ ] ; exact div_le_div_of_nonneg_right hω₂ ( by nlinarith ) ;
  have h_condExp_zero : ∀ᵐ ω ∂μ, (μ[fun ω' => lam * (M (t + 1) ω' - M t ω') | 𝓕 t]) ω = 0 := by
    have h_condExp_zero : ∀ᵐ ω ∂μ, (μ[fun ω' => M (t + 1) ω' - M t ω' | 𝓕 t]) ω = 0 := by
      convert martingale_increment_zero_condExp h_mart t using 1;
    have h_condExp_zero : ∀ᵐ ω ∂μ, (μ[fun ω' => lam * (M (t + 1) ω' - M t ω') | 𝓕 t]) ω = lam * (μ[fun ω' => M (t + 1) ω' - M t ω' | 𝓕 t]) ω := by
      apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
      · exact stronglyMeasurable_const;
      · exact MeasureTheory.Integrable.const_mul ( h_mart.integrable _ |> fun h => h.sub ( h_mart.integrable _ ) ) _;
      · exact MeasureTheory.Integrable.sub ( h_mart.integrable _ ) ( h_mart.integrable _ );
    filter_upwards [ h_condExp_zero, ‹∀ᵐ ω ∂μ, μ[fun ω' => M ( t + 1 ) ω' - M t ω' | ( 𝓕 t : MeasurableSpace Ω ) ] ω = 0› ] with ω hω₁ hω₂ using by rw [ hω₁, hω₂, MulZeroClass.mul_zero ] ;
  filter_upwards [ h_condExp_mono, h_condExp_add, h_condExp_mul, h_condExp_zero ] with ω hω₁ hω₂ hω₃ hω₄;
  exact hω₁.trans ( by rw [ hω₂, hω₄ ] ; linarith [ Real.add_one_le_exp ( V * lam ^ 2 / ( 2 * ( 1 - b / 3 * lam ) ) ), show lam ^ 2 * V / ( 2 * ( 1 - b / 3 * lam ) ) = V * lam ^ 2 / ( 2 * ( 1 - b / 3 * lam ) ) by ring ] )

/-- Construct a `SubGammaMG` from a martingale with bounded increments
and a uniform conditional variance bound. `process = M` definitionally. -/
noncomputable def subGammaMG_of_bounded_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : Martingale M 𝓕 μ)
    (b V : ℝ) (hb : 0 < b) (hV : 0 < V)
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |M (t + 1) ω - M t ω| ≤ b)
    (h_var : ∀ t, ∀ᵐ ω ∂μ,
      (μ[fun ω' => (M (t + 1) ω' - M t ω')^2 | 𝓕 t]) ω ≤ V)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0) :
    SubGammaMG V (b / 3) 𝓕 μ where
  process := M
  adapted := fun i =>
    (h_mart.stronglyMeasurable i).measurable
  integrable := h_mart.integrable
  integrable_exp := fun t lam _ =>
    integrable_exp_of_bounded_martingale h_mart hb h_bounded hM0 t lam
  increments_exp_integrable := fun t lam _ =>
    integrable_exp_increment_of_bounded h_mart (h_bounded t) lam
  increments_subGamma := fun t lam hlam_nn hlam =>
    condExp_exp_le_subGamma_form hb h_mart (h_bounded t) (h_var t) hlam_nn hlam
  increments_zero_mean := fun t => martingale_increment_zero_condExp h_mart t
  nu_pos := hV
  c_nonneg := by positivity


/-
**Bernstein's inequality** for iid bounded random variables
(corrected). Uses `iIndepFun` for mutual independence.
-/
theorem bernstein_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ} {sigma_sq : ℝ}
    (hb_pos : 0 < b) (hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (h_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (h_var_bound : ∀ t, ∫ ω, (X t ω)^2 ∂μ ≤ sigma_sq)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | (Finset.range n).sum (fun i => X i ω) ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (n * sigma_sq + b * eps / 3)))) := by
  by_cases h_sigma_sq : sigma_sq = 0;
  · -- Since $\sigma^2 = 0$, we have $X_i = 0$ almost surely for all $i$.
    have h_X_zero : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 := by
      intro i
      have h_X_zero_i : ∫ ω, X i ω ^ 2 ∂μ = 0 := by
        exact le_antisymm ( le_trans ( h_var_bound i ) h_sigma_sq.le ) ( MeasureTheory.integral_nonneg fun _ => sq_nonneg _ );
      rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ( fun _ => sq_nonneg _ ) ] at h_X_zero_i;
      · exact h_X_zero_i.mono fun ω hω => sq_eq_zero_iff.mp hω;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun ω => b ^ 2, by norm_num, by exact ( hX_meas i |> Measurable.pow_const <| 2 ) |> Measurable.aestronglyMeasurable, by filter_upwards [ h_bounded i ] with ω hω using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) hω 2 ];
    rw [ MeasureTheory.measure_mono_null ( fun ω hω => ?_ ) ( MeasureTheory.ae_all_iff.2 h_X_zero ) ] ; aesop;
    contrapose! hω; aesop;
  · by_cases hn : n = 0;
    · simp +decide [ hn, hε.not_ge ];
    · have h_mgf : ∀ lam : ℝ, 0 ≤ lam → lam * b < 3 → mgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ lam ≤ Real.exp (n * sigma_sq * lam ^ 2 / (2 * (1 - b * lam / 3))) := by
        intro lam hl hlam
        have h_mgf : mgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ lam = ∏ i ∈ Finset.range n, mgf (X i) μ lam := by
          convert h_indep.mgf_sum _ _;
          · rw [ Finset.sum_apply ];
          · assumption;
        have h_mgf_bound : ∀ i, mgf (X i) μ lam ≤ Real.exp (sigma_sq * lam ^ 2 / (2 * (1 - b * lam / 3))) := by
          exact fun i => mgf_le_subGamma_of_bounded ( hX_meas i ) hb_pos.le ( h_bounded i ) ( h_zero_mean i ) ( h_var_bound i ) hl ( by linarith );
        exact h_mgf.symm ▸ le_trans ( Finset.prod_le_prod ( fun _ _ => by exact MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ) fun _ _ => h_mgf_bound _ ) ( by simp +decide [ mul_assoc, mul_div_assoc, ← Real.exp_nat_mul ] );
      have h_chernoff : ∀ lam : ℝ, 0 ≤ lam → lam * b < 3 → μ {ω | ∑ i ∈ Finset.range n, X i ω ≥ eps} ≤ ENNReal.ofReal (Real.exp (-lam * eps) * Real.exp (n * sigma_sq * lam ^ 2 / (2 * (1 - b * lam / 3)))) := by
        intro lam hl hl';
        have := @ProbabilityTheory.measure_ge_le_exp_mul_mgf;
        convert ENNReal.ofReal_le_ofReal ( this eps hl _ ) |> le_trans <| ENNReal.ofReal_le_ofReal <| mul_le_mul_of_nonneg_left ( h_mgf lam hl hl' ) <| Real.exp_nonneg _ using 1;
        · simp +decide [ MeasureTheory.measureReal_def ];
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun ω => Real.exp ( lam * n * b );
          · norm_num;
          · exact Measurable.aestronglyMeasurable ( by measurability );
          · filter_upwards [ MeasureTheory.ae_all_iff.2 h_bounded ] with ω hω using by simpa using Real.exp_le_exp.2 ( show lam * ∑ i ∈ Finset.range n, X i ω ≤ lam * n * b by exact le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun _ _ => le_of_abs_le ( hω _ ) ) hl ) ( by simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ) ) ;
      convert h_chernoff ( eps / ( n * sigma_sq + b * eps / 3 ) ) ( by positivity ) ( by rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ show ( n : ℝ ) * sigma_sq > 0 by positivity ] ) using 1;
      rw [ ← Real.exp_add ] ; congr 1 ; field_simp ; ring;
      rw [ show ( eps * b * 2 + n * sigma_sq * 6 : ℝ ) = ( eps * n * sigma_sq * b * 6 + n ^ 2 * sigma_sq ^ 2 * 18 ) / ( n * sigma_sq * 3 ) by rw [ eq_div_iff ( by positivity ) ] ; ring ] ; norm_num ; ring


/-- **Freedman's inequality** (corrected): maximal Bernstein for martingales. -/
theorem freedman
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : MeasureTheory.Martingale M 𝓕 μ)
    (b : ℝ) (hb_pos : 0 < b)
    (h_bounded_increments : ∀ t, ∀ᵐ ω ∂μ,
      |M (t + 1) ω - M t ω| ≤ b)
    (V : ℝ) (hV_pos : 0 < V)
    (h_var : ∀ t, ∀ᵐ ω ∂μ,
      (μ[fun ω' => (M (t + 1) ω' - M t ω')^2 | 𝓕 t]) ω ≤ V)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0)
    {n : ℕ} (hn : 0 < n) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | ∃ t : ℕ, t ≤ n ∧ M t ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (↑n * V + b * eps / 3)))) := by
  -- Construct SubGammaMG V (b/3) from the bounded martingale.
  -- SG.process = M definitionally.
  let SG := subGammaMG_of_bounded_martingale h_mart b V hb_pos hV_pos
    h_bounded_increments h_var hM0
  -- Apply subGamma_ville_ineq directly.
  have h := subGamma_ville_ineq (M := SG) hM0 eps hε n hn
  -- The denominators differ only algebraically.
  -- 2 * V * ↑n + 2 * (b / 3) * eps = 2 * (↑n * V + b * eps / 3)
  convert h using 2
  field_simp


/-- **Bernstein for martingales** (corrected). Reduces to `freedman`. -/
theorem bernstein_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : MeasureTheory.Martingale M 𝓕 μ)
    (b : ℝ) (hb_pos : 0 < b)
    (h_bounded_increments : ∀ t, ∀ᵐ ω ∂μ,
      |M (t + 1) ω - M t ω| ≤ b)
    (V : ℝ) (hV_pos : 0 < V)
    (h_var : ∀ t, ∀ᵐ ω ∂μ,
      (μ[fun ω' => (M (t + 1) ω' - M t ω')^2 | 𝓕 t]) ω ≤ V)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0)
    {n : ℕ} (hn : 0 < n) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | M n ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (↑n * V + b * eps / 3)))) :=
  calc μ {ω | M n ω ≥ eps}
      ≤ μ {ω | ∃ t : ℕ, t ≤ n ∧ M t ω ≥ eps} := by
        apply measure_mono; intro ω hω; exact ⟨n, le_refl _, hω⟩
    _ ≤ _ := freedman h_mart b hb_pos h_bounded_increments V hV_pos h_var hM0 hn eps hε

end Pythia