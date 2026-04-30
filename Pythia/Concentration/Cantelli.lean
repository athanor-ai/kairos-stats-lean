/-
Cantelli's inequality — one-sided Chebyshev.

For a real-valued random variable X with mean μ and variance σ², for
any t > 0:

    P(X - μ ≥ t) ≤ σ² / (σ² + t²)

This is uniformly tighter than the two-sided Chebyshev bound
P(|X - μ| ≥ t) ≤ σ²/t².

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring `Pythia.Concentration.Cantelli.cantelli_real`
in namespace `Pythia.Concentration.Cantelli`.
-/
import Mathlib

namespace Pythia.Concentration.Cantelli

open MeasureTheory ProbabilityTheory

/-! ### Helper lemmas -/

/-
If `x ≥ t` and `s ≥ 0`, then `(x + s)² ≥ (t + s)²`.
-/
lemma sq_add_le_sq_add {t s x : ℝ} (hs : 0 ≤ s) (ht : 0 < t) (hx : t ≤ x) :
    (t + s) ^ 2 ≤ (x + s) ^ 2 := by
      gcongr

/-- Set inclusion: `{ω | t ≤ X ω} ⊆ {ω | (t + s)² ≤ (X ω + s)²}` for `s ≥ 0`, `t > 0`. -/
lemma set_inclusion
    {Ω : Type*} (X : Ω → ℝ) {t s : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    {ω | t ≤ X ω} ⊆ {ω | (t + s) ^ 2 ≤ (X ω + s) ^ 2} :=
  fun _ hω => sq_add_le_sq_add hs ht hω

/-
For a probability measure with `E[X] = 0`,
`E[(X + s)²] = E[X²] + s²`.
-/
lemma expectation_shift_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX_int : Integrable X μ)
    (hX_sq_int : Integrable (fun ω => X ω ^ 2) μ)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (s : ℝ) :
    ∫ ω, (X ω + s) ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ) + s ^ 2 := by
      simp +decide only [add_sq];
      rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ] <;> norm_num [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, hX_int, hX_sq_int, hmean ];
      · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul hX_int _ ) _;
      · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul hX_int _ ) _

/-
The algebraic identity that ties the Markov bound (with optimal shift
`s = σ²/t`) to the Cantelli bound.
-/
lemma cantelli_algebra {σ2 t : ℝ} (hσ2 : 0 < σ2) (ht : 0 < t) :
    (σ2 + (σ2 / t) ^ 2) / (t + σ2 / t) ^ 2 = σ2 / (σ2 + t ^ 2) := by
      -- Combine and simplify the numerator and denominator.
      field_simp
      ring

/-
Integrability of the shifted square `(X + s)²` given integrability of `X`
and `X²`.
-/
lemma integrable_shift_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX_int : Integrable X μ)
    (hX_sq_int : Integrable (fun ω => X ω ^ 2) μ) (s : ℝ) :
    Integrable (fun ω => (X ω + s) ^ 2) μ := by
      ring_nf;
      exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add ( hX_int.mul_const _ |> MeasureTheory.Integrable.mul_const <| _ ) hX_sq_int ) ( MeasureTheory.integrable_const _ )

/-
Nonnegativity (a.e.) of a square function.
-/
lemma ae_nonneg_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X : Ω → ℝ) (s : ℝ) :
    0 ≤ᵐ[μ] fun ω => (X ω + s) ^ 2 := by
      exact Filter.Eventually.of_forall fun ω => sq_nonneg _

/-
Markov bound reformulated as a probability bound: for nonneg integrable `f`
and `ε > 0`, `μ.real {x | ε ≤ f x} ≤ (∫ f) / ε`.
-/
lemma markov_prob_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (f : Ω → ℝ)
    (hf_nn : 0 ≤ᵐ[μ] f) (hf_int : Integrable f μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {x | ε ≤ f x} ≤ (∫ x, f x ∂μ) / ε := by
      have := @MeasureTheory.mul_meas_ge_le_integral_of_nonneg;
      rw [ le_div_iff₀' hε ] ; exact this hf_nn hf_int ε

/-
Monotonicity of `μ.real` for probability measures.
-/
lemma measure_real_mono
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {S T : Set Ω} (hST : S ⊆ T) (_hS : MeasurableSet S) (_hT : MeasurableSet T) :
    μ.real S ≤ μ.real T := by
      exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono hST )

/-
Cantelli's one-sided tail bound (mean-zero form).

For a real-valued random variable `X` with `E[X] = 0` and second moment
`σ² = E[X²] > 0`, for any `t > 0`:

    P(X ≥ t) ≤ σ² / (σ² + t²)

The proof uses the auxiliary random variable `Y = (X + s)²` with the
optimal shift `s = σ²/t`, applying Markov's inequality to `Y`.
-/
theorem cantelli_real
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ_meas : Measure Ω) [IsProbabilityMeasure μ_meas]
    (X : Ω → ℝ)
    (hX_meas : Measurable X)
    (hX_int : Integrable X μ_meas)
    (hX_sq_int : Integrable (fun ω => X ω ^ 2) μ_meas)
    (hmean : ∫ ω, X ω ∂μ_meas = 0)
    (σ2 : ℝ)
    (hσ2 : σ2 = ∫ ω, X ω ^ 2 ∂μ_meas)
    (hσ2_pos : 0 < σ2)
    (t : ℝ) (ht : 0 < t) :
    μ_meas.real {ω | t ≤ X ω} ≤ σ2 / (σ2 + t ^ 2) := by
  -- Let $s = \frac{\sigma^2}{t}$.
  set s := σ2 / t with hs_def
  have hs_pos : 0 < s := by
    positivity
  have hs_sq : s^2 = σ2^2 / t^2 := by
    rw [ div_pow ]
  have hst_sq : (t + s)^2 = t^2 + 2 * t * s + s^2 := by
    ring
  have hst_sq_subst : (t + s)^2 = t^2 + 2 * σ2 + σ2^2 / t^2 := by
    rw [ hst_sq, hs_sq, mul_assoc, mul_div_cancel₀ _ ht.ne' ]
  have hst_sq_subst_simplified : (t + s)^2 = (σ2 + t^2)^2 / t^2 := by
    grind;
  have h_markov : μ_meas.real {ω | (t + s)^2 ≤ (X ω + s)^2} ≤ (∫ ω, (X ω + s)^2 ∂μ_meas) / (t + s)^2 := by
    apply markov_prob_bound;
    · exact Filter.Eventually.of_forall fun ω => sq_nonneg _;
    · exact integrable_shift_sq μ_meas X hX_int hX_sq_int s;
    · positivity;
  convert le_trans _ h_markov using 1;
  · rw [ expectation_shift_sq ] <;> norm_num [ hmean ];
    · grind;
    · exact hX_int;
    · lia;
  · apply_rules [ measure_real_mono, set_inclusion ];
    · positivity;
    · exact measurableSet_Ici;
    · exact measurableSet_le measurable_const ( Measurable.pow_const ( hX_meas.add_const s ) _ )

end Pythia.Concentration.Cantelli