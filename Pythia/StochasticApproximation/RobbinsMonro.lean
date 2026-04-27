/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Pythia.StochasticApproximation.RobbinsSiegmund

/-!
# Robbins–Monro Stochastic Approximation

This module formalises the **Robbins–Monro (1951)** stochastic-approximation convergence
theorem.

## References

* H. Robbins, S. Monro, *A Stochastic Approximation Method*, Ann. Math. Stat. 22
  (1951), 400–407.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal MeasureTheory

namespace Pythia.StochasticApproximation

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The Lyapunov function `V(x) = (x − θ)²`. -/
def lyapunovFun (θ : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (X n ω - θ) ^ 2

/-! ## One-step conditional-expectation bound -/

/-- **One-step Lyapunov estimate.** -/
theorem condExp_lyapunov_bound [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (θ σ_sq : ℝ)
    (hX_adapt : ∀ n, StronglyMeasurable[ℱ n] (X n))
    (hY_adapt : ∀ n, StronglyMeasurable[ℱ n] (Y n))
    (hX_int : ∀ n, Integrable (X n) μ)
    (hY_int : ∀ n, Integrable (Y n) μ)
    (hY_sq_int : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (recursion : ∀ n ω, X (n + 1) ω = X n ω - a n * Y n ω)
    (cond_mean : ∀ n, (μ[Y n|ℱ n]) =ᵐ[μ] fun ω => f (X n ω))
    (hσ_sq_nn : 0 ≤ σ_sq)
    (second_moment_bound : ∀ n,
      (μ[fun ω => (Y n ω) ^ 2|ℱ n]) ≤ᵐ[μ] fun _ => σ_sq)
    (n : ℕ) :
    (μ[lyapunovFun θ X (n + 1)|ℱ n]) ≤ᵐ[μ]
      fun ω => lyapunovFun θ X n ω
               - 2 * a n * (X n ω - θ) * f (X n ω)
               + (a n) ^ 2 * σ_sq := by
  simp_all +decide [ MeasureTheory.condExp ]
  refine' Filter.EventuallyLE.trans _ _
  exact fun ω => lyapunovFun θ X n ω - 2 * a n * ( X n ω - θ ) * ( Y n ω ) + a n ^ 2 * ( Y n ω ) ^ 2
  · unfold lyapunovFun
    split_ifs <;> simp_all +decide [ Filter.EventuallyLE, Filter.eventually_inf_principal ]
    · exact Filter.Eventually.of_forall fun ω => by linarith
    · rename_i h₁ h₂ h₃
      contrapose! h₃
      exact StronglyMeasurable.pow ( StronglyMeasurable.sub ( hX_adapt n ) ( StronglyMeasurable.mul stronglyMeasurable_const ( hY_adapt n ) ) |> StronglyMeasurable.sub <| stronglyMeasurable_const ) _
    · filter_upwards [ ] with ω using by nlinarith only [ sq_nonneg ( X n ω - θ - a n * Y n ω ) ]
    · exact Filter.Eventually.of_forall fun ω => by nlinarith only [ sq_nonneg ( X n ω - θ - a n * Y n ω ) ]
  · filter_upwards [ cond_mean n, second_moment_bound n ] with ω hω₁ hω₂
    split_ifs at * <;> simp_all +decide [ Filter.EventuallyEq, Filter.eventually_inf_principal ]
    · exact mul_le_mul_of_nonneg_left hω₂ ( sq_nonneg _ )
    · rename_i h; exact False.elim <| h <| by exact ( hY_adapt n |> StronglyMeasurable.pow <| 2 )
    · exact?
    · exact False.elim <| ‹¬ ( ℱ n : MeasurableSpace Ω ) ≤ m0› <| ℱ.le n

/-! ## Helper: Lyapunov function satisfies Robbins-Siegmund condition -/

/-
The Lyapunov function satisfies the Robbins-Siegmund inequality
  `𝔼[V(n+1)|ℱₙ] ≤ V(n) + aₙ²σ²`
after dropping the non-negative drift term.
-/
lemma lyapunov_RS_condition [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (θ σ_sq : ℝ)
    (hX_adapt : ∀ n, StronglyMeasurable[ℱ n] (X n))
    (hY_adapt : ∀ n, StronglyMeasurable[ℱ n] (Y n))
    (hX_int : ∀ n, Integrable (X n) μ)
    (hY_int : ∀ n, Integrable (Y n) μ)
    (hY_sq_int : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (recursion : ∀ n ω, X (n + 1) ω = X n ω - a n * Y n ω)
    (hf_root : f θ = 0)
    (hf_drift : ∀ x : ℝ, x ≠ θ → (x - θ) * f x > 0)
    (cond_mean : ∀ n, (μ[Y n|ℱ n]) =ᵐ[μ] fun ω => f (X n ω))
    (hσ_sq_nn : 0 ≤ σ_sq)
    (second_moment_bound : ∀ n,
      (μ[fun ω => (Y n ω) ^ 2|ℱ n]) ≤ᵐ[μ] fun _ => σ_sq)
    (ha_pos : ∀ n, 0 < a n)
    (n : ℕ) :
    μ[lyapunovFun θ X (n + 1)|ℱ n] ≤ᵐ[μ]
      fun ω => (1 + 0) * lyapunovFun θ X n ω + (a n) ^ 2 * σ_sq := by
  have h_condExp_V_step : (μ[lyapunovFun θ X (n + 1)|ℱ n]) ≤ᵐ[μ] (fun ω => lyapunovFun θ X n ω - 2 * a n * (X n ω - θ) * f (X n ω) + a n ^ 2 * σ_sq) := by
    convert condExp_lyapunov_bound ℱ X Y a f θ σ_sq _ _ _ _ _ recursion cond_mean hσ_sq_nn second_moment_bound n using 1;
    · exact?;
    · exact?;
    · assumption;
    · assumption;
    · exact?;
  filter_upwards [ h_condExp_V_step ] with ω hω using le_trans hω ( by norm_num; nlinarith [ ha_pos n, show 0 ≤ a n * ( X n ω - θ ) * f ( X n ω ) by exact if h : X n ω = θ then by simp +decide [ * ] else by nlinarith [ ha_pos n, hf_drift ( X n ω ) h ] ] )

/-! ## Helper: Lyapunov function converges a.s. -/

/-
The Lyapunov function converges a.s. to a finite limit.
-/
lemma lyapunov_ae_converges [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (θ σ_sq : ℝ)
    (hX_adapt : ∀ n, StronglyMeasurable[ℱ n] (X n))
    (hY_adapt : ∀ n, StronglyMeasurable[ℱ n] (Y n))
    (hX_int : ∀ n, Integrable (X n) μ)
    (hY_int : ∀ n, Integrable (Y n) μ)
    (hY_sq_int : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hV_int : ∀ n, Integrable (lyapunovFun θ X n) μ)
    (recursion : ∀ n ω, X (n + 1) ω = X n ω - a n * Y n ω)
    (hf_root : f θ = 0)
    (hf_drift : ∀ x : ℝ, x ≠ θ → (x - θ) * f x > 0)
    (cond_mean : ∀ n, (μ[Y n|ℱ n]) =ᵐ[μ] fun ω => f (X n ω))
    (hσ_sq_nn : 0 ≤ σ_sq)
    (second_moment_bound : ∀ n,
      (μ[fun ω => (Y n ω) ^ 2|ℱ n]) ≤ᵐ[μ] fun _ => σ_sq)
    (ha_pos : ∀ n, 0 < a n)
    (ha_sq : Summable (fun n => (a n) ^ 2)) :
    ∃ V_inf : Ω → ℝ,
      ∀ᵐ ω ∂μ, Tendsto (fun n => lyapunovFun θ X n ω) atTop (𝓝 (V_inf ω)) := by
  convert robbins_siegmund ℱ ( lyapunovFun θ X ) ( fun n => 0 ) ( fun n => ( a n ) ^ 2 * σ_sq ) _ _ _ _ _ _ _ _ using 1;
  all_goals try exact ha_sq.mul_right _;
  bv_omega;
  exact fun n => by exact StronglyMeasurable.pow ( hX_adapt n |> StronglyMeasurable.sub <| stronglyMeasurable_const ) _;
  exact fun n => Filter.Eventually.of_forall fun ω => sq_nonneg _;
  · assumption;
  · exact fun _ => le_rfl;
  · exact summable_zero;
  · exact fun n => mul_nonneg ( sq_nonneg _ ) hσ_sq_nn;
  · convert lyapunov_RS_condition ℱ X Y a f θ σ_sq _ _ _ _ _ _ _ _ _ _ _ using 1;
    all_goals tauto

/-! ## Helper: V∞ = 0 from convergence + drift -/

/-
If `(xₙ - θ)²` converges to `c ≥ 0` and `∑ aₙ (xₙ - θ) f(xₙ) < ∞`
with `f` continuous, `(x-θ)f(x) > 0` for `x ≠ θ`, and `∑ aₙ = ∞`,
then `c = 0`. This is purely a real-analysis lemma.
-/
lemma limit_eq_zero_of_drift_summable
    {x : ℕ → ℝ} {a : ℕ → ℝ} {f : ℝ → ℝ} {θ c : ℝ}
    (hf_cont : Continuous f)
    (hf_root : f θ = 0)
    (hf_drift : ∀ y : ℝ, y ≠ θ → (y - θ) * f y > 0)
    (ha_pos : ∀ n, 0 < a n)
    (ha_div : ¬Summable a)
    (hc_nn : 0 ≤ c)
    (hx_conv : Tendsto (fun n => (x n - θ) ^ 2) atTop (𝓝 c))
    (h_drift_sum : Summable (fun n => a n * (x n - θ) * f (x n))) :
    c = 0 := by
  by_contra h_c_pos
  have h_compact : ∃ N, ∀ n ≥ N, |x n - θ| ≥ Real.sqrt (c / 2) ∧ |x n - θ| ≤ Real.sqrt (2 * c) := by
    -- By definition of limit, there exists an N such that for all n ≥ N, |(x n - θ)^2 - c| < c/2.
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, |(x n - θ)^2 - c| < c / 2 := by
      exact Metric.tendsto_atTop.mp hx_conv ( c / 2 ) ( half_pos ( lt_of_le_of_ne hc_nn ( Ne.symm h_c_pos ) ) );
    exact ⟨ N, fun n hn => ⟨ Real.sqrt_le_iff.mpr ⟨ by positivity, by cases abs_cases ( x n - θ ) <;> nlinarith [ abs_lt.mp ( hN n hn ) ] ⟩, Real.abs_le_sqrt <| by cases abs_cases ( x n - θ ) <;> nlinarith [ abs_lt.mp ( hN n hn ) ] ⟩ ⟩;
  obtain ⟨N, hN⟩ := h_compact
  have h_min : ∃ δ > 0, ∀ n ≥ N, (x n - θ) * f (x n) ≥ δ := by
    have h_compact : IsCompact {y : ℝ | Real.sqrt (c / 2) ≤ |y - θ| ∧ |y - θ| ≤ Real.sqrt (2 * c)} := by
      refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
      exact ⟨ isClosed_Icc.preimage ( continuous_abs.comp ( continuous_sub_right _ ) ), isBounded_iff_forall_norm_le.mpr ⟨ Real.sqrt ( 2 * c ) + |θ|, by rintro y ⟨ hy₁, hy₂ ⟩ ; exact abs_le.mpr ⟨ by cases abs_cases θ <;> cases abs_cases ( y - θ ) <;> linarith, by cases abs_cases θ <;> cases abs_cases ( y - θ ) <;> linarith ⟩ ⟩ ⟩;
    have h_min : ∃ δ ∈ (Set.image (fun y => (y - θ) * f y) {y : ℝ | Real.sqrt (c / 2) ≤ |y - θ| ∧ |y - θ| ≤ Real.sqrt (2 * c)}), ∀ z ∈ (Set.image (fun y => (y - θ) * f y) {y : ℝ | Real.sqrt (c / 2) ≤ |y - θ| ∧ |y - θ| ≤ Real.sqrt (2 * c)}), δ ≤ z := by
      apply_rules [ IsCompact.exists_isLeast, h_compact ];
      · exact h_compact.image ( Continuous.mul ( continuous_id.sub continuous_const ) hf_cont );
      · exact ⟨ _, ⟨ x N, hN N le_rfl, rfl ⟩ ⟩;
    obtain ⟨ δ, hδ₁, hδ₂ ⟩ := h_min;
    exact ⟨ δ, by obtain ⟨ y, hy₁, rfl ⟩ := hδ₁; exact hf_drift y ( by rintro rfl; exact absurd hy₁.1 ( by norm_num; positivity ) ), fun n hn => hδ₂ _ <| Set.mem_image_of_mem _ <| hN n hn ⟩;
  obtain ⟨δ, hδ_pos, hδ⟩ := h_min
  have h_sum_div : ¬ Summable (fun n => a n * δ) := by
    rw [ summable_mul_right_iff ] <;> aesop;
  rw [ ← summable_nat_add_iff N ] at *;
  exact h_sum_div <| Summable.of_nonneg_of_le ( fun n => mul_nonneg ( le_of_lt ( ha_pos _ ) ) hδ_pos.le ) ( fun n => by nlinarith [ ha_pos ( n + N ), hδ ( n + N ) ( by linarith ) ] ) h_drift_sum

/-
If `(xₙ - θ)²` converges to `0`, then `xₙ → θ`.
-/
lemma tendsto_of_sq_tendsto_zero
    {x : ℕ → ℝ} {θ : ℝ}
    (h : Tendsto (fun n => (x n - θ) ^ 2) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 θ) := by
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ( by simpa [ Real.sqrt_sq_eq_abs ] using h.sqrt )

/-! ## Helper: pointwise drift summability -/

/-
The drift series `∑ aₙ (Xₙ-θ) f(Xₙ)` converges a.e.
Proof: integral bound from Lyapunov inequality + Tonelli theorem.
-/
lemma drift_summable_ae [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (θ σ_sq : ℝ)
    (hf_cont : Continuous f)
    (hX_adapt : ∀ n, StronglyMeasurable[ℱ n] (X n))
    (hY_adapt : ∀ n, StronglyMeasurable[ℱ n] (Y n))
    (hX_int : ∀ n, Integrable (X n) μ)
    (hY_int : ∀ n, Integrable (Y n) μ)
    (hY_sq_int : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hV_int : ∀ n, Integrable (lyapunovFun θ X n) μ)
    (recursion : ∀ n ω, X (n + 1) ω = X n ω - a n * Y n ω)
    (hf_root : f θ = 0)
    (hf_drift : ∀ x : ℝ, x ≠ θ → (x - θ) * f x > 0)
    (cond_mean : ∀ n, (μ[Y n|ℱ n]) =ᵐ[μ] fun ω => f (X n ω))
    (hσ_sq_nn : 0 ≤ σ_sq)
    (second_moment_bound : ∀ n,
      (μ[fun ω => (Y n ω) ^ 2|ℱ n]) ≤ᵐ[μ] fun _ => σ_sq)
    (ha_pos : ∀ n, 0 < a n)
    (ha_sq : Summable (fun n => (a n) ^ 2)) :
    ∀ᵐ ω ∂μ, Summable (fun n => a n * (X n ω - θ) * f (X n ω)) := by
  have h_summable : Summable (fun n => ∫ ω, (a n * (X n ω - θ) * f (X n ω)) ∂μ) := by
    have h_summable : ∀ n, ∫ ω, (lyapunovFun θ X (n + 1) ω) ∂μ ≤ ∫ ω, (lyapunovFun θ X n ω) ∂μ - 2 * a n * ∫ ω, (X n ω - θ) * f (X n ω) ∂μ + (a n) ^ 2 * σ_sq := by
      intro n;
      have := condExp_lyapunov_bound ℱ X Y a f θ σ_sq hX_adapt hY_adapt hX_int hY_int hY_sq_int recursion cond_mean hσ_sq_nn second_moment_bound n;
      convert MeasureTheory.integral_mono_ae _ _ this using 1;
      · rw [ MeasureTheory.integral_condExp ];
      · rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] <;> norm_num;
        · simp +decide only [mul_assoc, integral_const_mul];
        · exact hV_int n;
        · have h_integrable : Integrable (fun ω => (X n ω - θ) * f (X n ω)) μ := by
            have h_integrable : Integrable (fun ω => (X n ω - θ) ^ 2 + f (X n ω) ^ 2) μ := by
              refine' MeasureTheory.Integrable.add _ _;
              · exact hV_int n;
              · have h_integrable : Integrable (fun ω => (μ[Y n | ℱ n] ω) ^ 2) μ := by
                  refine' MeasureTheory.MemLp.integrable_sq _;
                  refine' MeasureTheory.MemLp.condExp _;
                  rw [ memLp_two_iff_integrable_sq ] ; aesop;
                  exact hY_int n |> MeasureTheory.Integrable.aestronglyMeasurable;
                exact h_integrable.congr ( by filter_upwards [ cond_mean n ] with ω hω; aesop );
            refine' h_integrable.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.sub ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) ) ( hf_cont.comp_aestronglyMeasurable ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable ) );
            · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
          convert h_integrable.const_mul ( 2 * a n ) using 2 ; ring;
        · refine' MeasureTheory.Integrable.sub ( hV_int n ) _;
          have h_integrable : Integrable (fun ω => (X n ω - θ) * f (X n ω)) μ := by
            have h_integrable : Integrable (fun ω => (X n ω - θ) ^ 2 + f (X n ω) ^ 2) μ := by
              refine' MeasureTheory.Integrable.add _ _;
              · exact hV_int n;
              · have h_integrable : Integrable (fun ω => (μ[Y n | ℱ n] ω) ^ 2) μ := by
                  refine' MeasureTheory.MemLp.integrable_sq _;
                  refine' MeasureTheory.MemLp.condExp _;
                  rw [ memLp_two_iff_integrable_sq ] ; aesop;
                  exact hY_int n |> MeasureTheory.Integrable.aestronglyMeasurable;
                exact h_integrable.congr ( by filter_upwards [ cond_mean n ] with ω hω; aesop );
            refine' h_integrable.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.sub ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) ) ( hf_cont.comp_aestronglyMeasurable ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable ) );
            · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
          convert h_integrable.const_mul ( 2 * a n ) using 2 ; ring;
        · exact MeasureTheory.integrable_const _;
      · exact MeasureTheory.integrable_condExp;
      · apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.neg, MeasureTheory.Integrable.mul_const, MeasureTheory.Integrable.const_mul ];
        · have h_integrable : Integrable (fun ω => (X n ω - θ) * f (X n ω)) μ := by
            have h_integrable : Integrable (fun ω => (X n ω - θ) ^ 2 + f (X n ω) ^ 2) μ := by
              refine' MeasureTheory.Integrable.add _ _;
              · exact hV_int n;
              · have h_integrable : Integrable (fun ω => (μ[Y n | ℱ n] ω) ^ 2) μ := by
                  refine' MeasureTheory.MemLp.integrable_sq _;
                  refine' MeasureTheory.MemLp.condExp _;
                  rw [ memLp_two_iff_integrable_sq ] ; aesop;
                  exact hY_int n |> MeasureTheory.Integrable.aestronglyMeasurable;
                exact h_integrable.congr ( by filter_upwards [ cond_mean n ] with ω hω; aesop );
            refine' h_integrable.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.sub ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) ) ( hf_cont.comp_aestronglyMeasurable ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable ) );
            · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
          convert h_integrable.const_mul ( 2 * a n ) using 2 ; ring;
        · exact MeasureTheory.integrable_const _;
    have h_summable : ∀ N, ∑ n ∈ Finset.range N, (a n * ∫ ω, (X n ω - θ) * f (X n ω) ∂μ) ≤ (1 / 2) * (∫ ω, (lyapunovFun θ X 0 ω) ∂μ) + (1 / 2) * (∑ n ∈ Finset.range N, (a n) ^ 2 * σ_sq) := by
      intro N
      have h_summable : ∑ n ∈ Finset.range N, (2 * a n * ∫ ω, (X n ω - θ) * f (X n ω) ∂μ) ≤ (∫ ω, (lyapunovFun θ X 0 ω) ∂μ) - (∫ ω, (lyapunovFun θ X N ω) ∂μ) + ∑ n ∈ Finset.range N, (a n) ^ 2 * σ_sq := by
        induction' N with N ih <;> norm_num [ Finset.sum_range_succ ] at *;
        linarith [ h_summable N ];
      norm_num [ Finset.mul_sum _ _ _, mul_assoc ] at *;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at * ; linarith [ show 0 ≤ ∫ ω, lyapunovFun θ X N ω ∂μ from MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ];
    have h_summable : Summable (fun n => a n * ∫ ω, (X n ω - θ) * f (X n ω) ∂μ) := by
      rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
      · norm_num [ Filter.tendsto_atTop_atTop ];
        exact ⟨ 1 / 2 * ∫ ω, lyapunovFun θ X 0 ω ∂μ + 1 / 2 * ∑' n, a n ^ 2 * σ_sq + 1, fun N => ⟨ N, le_rfl, lt_of_le_of_lt ( h_summable N ) ( by linarith [ show ∑ n ∈ Finset.range N, a n ^ 2 * σ_sq ≤ ∑' n, a n ^ 2 * σ_sq from Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ => mul_nonneg ( sq_nonneg _ ) hσ_sq_nn ) ( by simpa only [ ← Finset.sum_mul _ _ _ ] using ha_sq.mul_right _ ) ] ) ⟩ ⟩;
      · intro n;
        refine' mul_nonneg ( le_of_lt ( ha_pos n ) ) ( MeasureTheory.integral_nonneg_of_ae _ );
        filter_upwards [ ] with ω using if h : X n ω = θ then by simp +decide [ h, hf_root ] else le_of_lt ( hf_drift _ h );
    simpa only [ mul_assoc, MeasureTheory.integral_const_mul ] using h_summable;
  have h_integrable : ∀ n, Integrable (fun ω => a n * (X n ω - θ) * f (X n ω)) μ := by
    intro n;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun ω => a n ^ 2 * ( X n ω - θ ) ^ 2 + ( f ( X n ω ) ) ^ 2;
    · refine' MeasureTheory.Integrable.add _ _;
      · exact MeasureTheory.Integrable.const_mul ( hV_int n ) _;
      · have h_integrable_f : Integrable (fun ω => (μ[Y n | ℱ n] ω) ^ 2) μ := by
          refine' MeasureTheory.MemLp.integrable_sq _;
          refine' MeasureTheory.MemLp.condExp _;
          rw [ memLp_two_iff_integrable_sq ] ; aesop;
          exact hY_int n |> Integrable.aestronglyMeasurable;
        exact h_integrable_f.congr ( by filter_upwards [ cond_mean n ] with ω hω; aesop );
    · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable |> fun h => h.sub ( MeasureTheory.aestronglyMeasurable_const ) ) ) ( hf_cont.comp_aestronglyMeasurable ( hX_int n |> MeasureTheory.Integrable.aestronglyMeasurable ) );
    · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( a n * ( X n ω - θ ) - f ( X n ω ) ), sq_nonneg ( a n * ( X n ω - θ ) + f ( X n ω ) ) ], by nlinarith only [ sq_nonneg ( a n * ( X n ω - θ ) - f ( X n ω ) ), sq_nonneg ( a n * ( X n ω - θ ) + f ( X n ω ) ) ] ⟩;
  have h_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω => a n * (X n ω - θ) * f (X n ω) := by
    intro n; filter_upwards [ ] with ω; by_cases h : X n ω = θ <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    linarith [ hf_drift ( X n ω ) h ];
  have h_summable : ∫⁻ ω, ∑' n, ENNReal.ofReal (a n * (X n ω - θ) * f (X n ω)) ∂μ < ⊤ := by
    rw [ MeasureTheory.lintegral_tsum ];
    · have h_summable : ∀ n, ∫⁻ ω, ENNReal.ofReal (a n * (X n ω - θ) * f (X n ω)) ∂μ = ENNReal.ofReal (∫ ω, a n * (X n ω - θ) * f (X n ω) ∂μ) := by
        intro n;
        rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · exact h_integrable n;
        · exact h_nonneg n;
      simp_all +decide [ ENNReal.ofReal_sum_of_nonneg ];
      exact?;
    · exact fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable ( h_integrable n |> Integrable.aemeasurable );
  have h_summable : ∀ᵐ ω ∂μ, ∑' n, ENNReal.ofReal (a n * (X n ω - θ) * f (X n ω)) < ⊤ := by
    rw [ MeasureTheory.ae_iff ];
    contrapose! h_summable;
    refine' le_trans _ ( MeasureTheory.setLIntegral_le_lintegral _ _ );
    swap;
    exact { a_1 : Ω | ∞ ≤ ∑' n, ENNReal.ofReal ( a n * ( X n a_1 - θ ) * f ( X n a_1 ) ) };
    refine' le_trans _ ( MeasureTheory.setLIntegral_mono_ae _ _ );
    rotate_left;
    use fun ω => ∞;
    · refine' AEMeasurable.ennreal_tsum _;
      exact fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable ( h_integrable n |> Integrable.aemeasurable ) |> fun h => h.mono_measure <| Measure.restrict_le_self;
    · exact Filter.Eventually.of_forall fun x hx => hx;
    · simp +decide [ h_summable ];
      rw [ ENNReal.mul_eq_top ] ; aesop;
  filter_upwards [ h_summable, MeasureTheory.ae_all_iff.2 h_nonneg ] with ω hω₁ hω₂;
  convert ENNReal.summable_toReal _;
  rotate_left;
  use fun n => ENNReal.ofReal ( a n * ( X n ω - θ ) * f ( X n ω ) );
  · exact ne_of_lt hω₁;
  · rw [ ENNReal.toReal_ofReal ( hω₂ _ ) ]

/-! ## Main convergence theorem -/

/-
**Robbins–Monro convergence theorem (Robbins–Monro 1951).**

Let `X : ℕ → Ω → ℝ` satisfy `X(n+1) = X(n) − a(n) Y(n)`, where:
* `f` is continuous with `f(θ) = 0` and `(x − θ) f(x) > 0` for `x ≠ θ`,
* `𝔼[Y(n) | ℱ(n)] = f(X(n))` a.s.,
* `𝔼[Y(n)² | ℱ(n)] ≤ σ²` a.s.,
* `∑ a(n) = ∞` and `∑ a(n)² < ∞`.

Then `X(n) → θ` almost surely.
-/
theorem robbins_monro_ae_tendsto [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (θ σ_sq : ℝ)
    (hf_cont : Continuous f)
    (hX_adapt : ∀ n, StronglyMeasurable[ℱ n] (X n))
    (hY_adapt : ∀ n, StronglyMeasurable[ℱ n] (Y n))
    (hX_int : ∀ n, Integrable (X n) μ)
    (hY_int : ∀ n, Integrable (Y n) μ)
    (hY_sq_int : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hV_int : ∀ n, Integrable (lyapunovFun θ X n) μ)
    (recursion : ∀ n ω, X (n + 1) ω = X n ω - a n * Y n ω)
    (hf_root : f θ = 0)
    (hf_drift : ∀ x : ℝ, x ≠ θ → (x - θ) * f x > 0)
    (cond_mean : ∀ n, (μ[Y n|ℱ n]) =ᵐ[μ] fun ω => f (X n ω))
    (hσ_sq_nn : 0 ≤ σ_sq)
    (second_moment_bound : ∀ n,
      (μ[fun ω => (Y n ω) ^ 2|ℱ n]) ≤ᵐ[μ] fun _ => σ_sq)
    (ha_pos : ∀ n, 0 < a n)
    (ha_div : ¬Summable a)
    (ha_sq : Summable (fun n => (a n) ^ 2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 θ) := by
  -- Step 1: V converges a.s.
  obtain ⟨V_inf, hV_inf⟩ := lyapunov_ae_converges ℱ X Y a f θ σ_sq
    hX_adapt hY_adapt hX_int hY_int hY_sq_int hV_int recursion
    hf_root hf_drift cond_mean hσ_sq_nn second_moment_bound ha_pos ha_sq
  -- Step 2: ∑ aₙ(Xₙ-θ)f(Xₙ) < ∞ a.e. (from integral bound + Tonelli)
  -- Step 3: V∞ = 0 a.e. (from limit_eq_zero_of_drift_summable)
  -- Step 4: Xₙ → θ a.e. (from tendsto_of_sq_tendsto_zero)
  filter_upwards [ hV_inf, drift_summable_ae ℱ X Y a f θ σ_sq hf_cont hX_adapt hY_adapt hX_int hY_int hY_sq_int hV_int recursion hf_root hf_drift cond_mean hσ_sq_nn second_moment_bound ha_pos ha_sq ] with ω hω₁ hω₂;
  convert tendsto_of_sq_tendsto_zero _;
  convert hω₁ using 1;
  rw [ limit_eq_zero_of_drift_summable hf_cont hf_root hf_drift ha_pos ha_div ( le_of_tendsto_of_tendsto' tendsto_const_nhds hω₁ fun n => sq_nonneg _ ) hω₁ hω₂ ]

end

end Pythia.StochasticApproximation