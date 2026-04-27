/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Robbins–Siegmund Almost-Supermartingale Convergence

This file proves the **Robbins–Siegmund lemma**: if a non-negative adapted process
`V` satisfies `𝔼[V(n+1)|ℱₙ] ≤ (1 + αₙ) V(n) + βₙ` a.e. with `∑ αₙ < ∞` and
`∑ βₙ < ∞`, then `V(n)` converges a.s. to a finite limit.

The proof constructs a genuine non-negative supermartingale
  `S(n) = (V(n) + Rₙ) / Pₙ`
where `Rₙ = ∑_{k≥n} βₖ` and `Pₙ = ∏_{k<n}(1+αₖ)`, then applies Doob's
supermartingale convergence theorem.

## References

* H. Robbins, D. Siegmund, *A convergence theorem for non-negative almost
  supermartingales and some applications*, 1971.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal MeasureTheory

namespace Pythia.StochasticApproximation

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Helper: tail sums and partial products -/

/-- Tail sum `R n = ∑_{k≥0} β(n+k)`. -/
private def tailSum (β : ℕ → ℝ) (n : ℕ) : ℝ := ∑' k, β (n + k)

/-- Partial product `P n = ∏_{k<n}(1 + α k)`. -/
private def partialProd (α : ℕ → ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (1 + α k)

private lemma tailSum_nonneg {β : ℕ → ℝ} (hβ_nn : ∀ n, 0 ≤ β n) (n : ℕ) :
    0 ≤ tailSum β n :=
  tsum_nonneg fun k => hβ_nn _

private lemma tailSum_step {β : ℕ → ℝ} (hβ_sum : Summable β) (n : ℕ) :
    tailSum β n = β n + tailSum β (n + 1) := by
  convert Summable.tsum_eq_zero_add _;
  · exact tsum_congr fun k => by ring;
  · infer_instance;
  · infer_instance;
  · exact hβ_sum.comp_injective ( add_right_injective n )

private lemma tailSum_tendsto_zero {β : ℕ → ℝ} (hβ_sum : Summable β) :
    Tendsto (tailSum β) atTop (𝓝 0) := by
  convert tendsto_sum_nat_add ( fun n => β n ) using 1;
  exact funext fun n => tsum_congr fun k => by ring;

private lemma partialProd_pos {α : ℕ → ℝ} (hα_nn : ∀ n, 0 ≤ α n) (n : ℕ) :
    0 < partialProd α n :=
  Finset.prod_pos fun k _ => by linarith [hα_nn k]

private lemma partialProd_step {α : ℕ → ℝ} (n : ℕ) :
    partialProd α (n + 1) = partialProd α n * (1 + α n) := by
  simp [partialProd, Finset.prod_range_succ]

private lemma partialProd_le_exp_tsum {α : ℕ → ℝ} (hα_nn : ∀ n, 0 ≤ α n)
    (hα_sum : Summable α) (n : ℕ) :
    partialProd α n ≤ Real.exp (∑' k, α k) := by
  unfold partialProd
  calc ∏ k ∈ Finset.range n, (1 + α k)
      ≤ ∏ k ∈ Finset.range n, Real.exp (α k) :=
        Finset.prod_le_prod (fun k _ => by linarith [hα_nn k])
          (fun k _ => by rw [add_comm]; exact Real.add_one_le_exp _)
    _ = Real.exp (∑ k ∈ Finset.range n, α k) := by rw [Real.exp_sum]
    _ ≤ Real.exp (∑' k, α k) :=
        Real.exp_le_exp_of_le (Summable.sum_le_tsum _ (fun _ _ => hα_nn _) hα_sum)

private lemma partialProd_convergent {α : ℕ → ℝ} (hα_nn : ∀ n, 0 ≤ α n)
    (hα_sum : Summable α) :
    ∃ P_inf : ℝ, 0 < P_inf ∧
      Tendsto (partialProd α) atTop (𝓝 P_inf) := by
  -- The partial products are bounded below by 1, which is finite. By Monotone Convergence (either via Monotone.tendsto_atTop_iSup or via tendsto_atTop_isLUB), they converge.
  have h_partialProd_bounded : BddAbove (Set.range (partialProd α)) := by
    exact ⟨ _, Set.forall_mem_range.mpr fun n => partialProd_le_exp_tsum hα_nn hα_sum n ⟩;
  exact ⟨ _, lt_of_lt_of_le zero_lt_one <| le_csSup h_partialProd_bounded ⟨ 0, rfl ⟩, tendsto_atTop_isLUB ( monotone_nat_of_le_succ fun n => by rw [ partialProd_step ] ; exact le_mul_of_one_le_right ( show 0 ≤ partialProd α n from le_of_lt <| partialProd_pos hα_nn n ) <| by linarith [ hα_nn n ] ) ( isLUB_ciSup h_partialProd_bounded ) ⟩

/-! ### The modified supermartingale -/

/-- The modified process `S(n,ω) = (V(n,ω) + R(n)) / P(n)`. -/
private def modifiedProcess (V : ℕ → Ω → ℝ) (α β : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (V n ω + tailSum β n) / partialProd α n

private lemma modifiedProcess_nonneg {V : ℕ → Ω → ℝ} {α β : ℕ → ℝ}
    (hV_nn : ∀ n, 0 ≤ᵐ[μ] V n) (hα_nn : ∀ n, 0 ≤ α n)
    (hβ_nn : ∀ n, 0 ≤ β n) (n : ℕ) :
    0 ≤ᵐ[μ] modifiedProcess V α β n := by
  filter_upwards [hV_nn n] with ω hω
  exact div_nonneg (add_nonneg hω (tailSum_nonneg hβ_nn n))
    (le_of_lt (partialProd_pos hα_nn n))

private lemma modifiedProcess_adapted {V : ℕ → Ω → ℝ} {α β : ℕ → ℝ}
    {ℱ : Filtration ℕ m0}
    (hV_adapt : ∀ n, StronglyMeasurable[ℱ n] (V n)) (n : ℕ) :
    StronglyMeasurable[ℱ n] (modifiedProcess V α β n) := by
  unfold modifiedProcess
  exact ((hV_adapt n).add stronglyMeasurable_const).mul_const _

private lemma modifiedProcess_integrable {V : ℕ → Ω → ℝ} {α β : ℕ → ℝ}
    (hV_int : ∀ n, Integrable (V n) μ) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (modifiedProcess V α β n) μ := by
  exact ((hV_int n).add (integrable_const _)).div_const _

/-
One-step supermartingale inequality for the modified process.
-/
private lemma modifiedProcess_condExp_le [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {V : ℕ → Ω → ℝ} {α β : ℕ → ℝ}
    (hV_adapt : ∀ n, StronglyMeasurable[ℱ n] (V n))
    (hV_nn : ∀ n, 0 ≤ᵐ[μ] V n)
    (hV_int : ∀ n, Integrable (V n) μ)
    (hα_nn : ∀ n, 0 ≤ α n)
    (hα_sum : Summable α)
    (hβ_nn : ∀ n, 0 ≤ β n)
    (hβ_sum : Summable β)
    (h_cond : ∀ n,
      μ[V (n + 1)|ℱ n] ≤ᵐ[μ] fun ω => (1 + α n) * V n ω + β n)
    (n : ℕ) :
    μ[modifiedProcess V α β (n + 1)|ℱ n] ≤ᵐ[μ]
      modifiedProcess V α β n := by
  refine' Filter.EventuallyLE.trans _ _;
  exact fun ω => ( μ[V ( n + 1 ) | ℱ n] ω + tailSum β ( n + 1 ) ) / partialProd α ( n + 1 );
  · have h_cond_exp : μ[fun ω => V (n + 1) ω + tailSum β (n + 1) | ℱ n] =ᶠ[ae μ] fun ω => μ[V (n + 1) | ℱ n] ω + tailSum β (n + 1) := by
      convert MeasureTheory.condExp_add _ _ _ using 1;
      · rw [ MeasureTheory.condExp_const ] ; aesop;
        exact?;
      · exact hV_int _;
      · exact MeasureTheory.integrable_const _;
    have h_cond_exp : μ[fun ω => (V (n + 1) ω + tailSum β (n + 1)) / partialProd α (n + 1) | ℱ n] =ᶠ[ae μ] fun ω => (μ[V (n + 1) | ℱ n] ω + tailSum β (n + 1)) / partialProd α (n + 1) := by
      have h_cond_exp : μ[fun ω => (V (n + 1) ω + tailSum β (n + 1)) / partialProd α (n + 1) | ℱ n] =ᵐ[μ] fun ω => μ[fun ω => V (n + 1) ω + tailSum β (n + 1) | ℱ n] ω / partialProd α (n + 1) := by
        convert MeasureTheory.condExp_mul_of_stronglyMeasurable_right _ _ _ using 1;
        · exact?;
        · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.add ( hV_int _ ) ( MeasureTheory.integrable_const _ ) ) _;
        · exact MeasureTheory.Integrable.add ( hV_int _ ) ( MeasureTheory.integrable_const _ );
      filter_upwards [ h_cond_exp, ‹μ[fun ω => V ( n + 1 ) ω + tailSum β ( n + 1 ) | ℱ n] =ᶠ[ae μ] fun ω => μ[V ( n + 1 ) | ℱ n] ω + tailSum β ( n + 1 ) › ] with ω hω₁ hω₂ using by aesop;
    exact h_cond_exp.le;
  · filter_upwards [ h_cond n ] with ω hω;
    unfold modifiedProcess;
    rw [ div_le_div_iff₀ ];
    · rw [ partialProd_step ];
      rw [ show tailSum β n = β n + tailSum β ( n + 1 ) from tailSum_step hβ_sum n ];
      nlinarith [ hα_nn n, hβ_nn n, tailSum_nonneg hβ_nn ( n + 1 ), partialProd_pos hα_nn n, mul_le_mul_of_nonneg_right ( hα_nn n ) ( partialProd_pos hα_nn n |> le_of_lt ), mul_le_mul_of_nonneg_right ( hβ_nn n ) ( partialProd_pos hα_nn n |> le_of_lt ) ];
    · exact?;
    · exact?

/-- The modified process is a supermartingale. -/
private lemma modifiedProcess_supermartingale [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {V : ℕ → Ω → ℝ} {α β : ℕ → ℝ}
    (hV_adapt : ∀ n, StronglyMeasurable[ℱ n] (V n))
    (hV_nn : ∀ n, 0 ≤ᵐ[μ] V n)
    (hV_int : ∀ n, Integrable (V n) μ)
    (hα_nn : ∀ n, 0 ≤ α n)
    (hα_sum : Summable α)
    (hβ_nn : ∀ n, 0 ≤ β n)
    (hβ_sum : Summable β)
    (h_cond : ∀ n,
      μ[V (n + 1)|ℱ n] ≤ᵐ[μ] fun ω => (1 + α n) * V n ω + β n) :
    Supermartingale (modifiedProcess V α β) ℱ μ := by
  exact supermartingale_nat
    (fun n => modifiedProcess_adapted hV_adapt n)
    (fun n => modifiedProcess_integrable hV_int n)
    (fun n => modifiedProcess_condExp_le hV_adapt hV_nn hV_int
      hα_nn hα_sum hβ_nn hβ_sum h_cond n)

/-
L¹ bound on the modified process (from supermartingale property).
-/
private lemma modifiedProcess_eLpNorm_bound [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {V : ℕ → Ω → ℝ} {α β : ℕ → ℝ}
    (hV_adapt : ∀ n, StronglyMeasurable[ℱ n] (V n))
    (hV_nn : ∀ n, 0 ≤ᵐ[μ] V n)
    (hV_int : ∀ n, Integrable (V n) μ)
    (hα_nn : ∀ n, 0 ≤ α n)
    (hα_sum : Summable α)
    (hβ_nn : ∀ n, 0 ≤ β n)
    (hβ_sum : Summable β)
    (h_cond : ∀ n,
      μ[V (n + 1)|ℱ n] ≤ᵐ[μ] fun ω => (1 + α n) * V n ω + β n)
    (n : ℕ) :
    eLpNorm (modifiedProcess V α β n) 1 μ
      ≤ eLpNorm (modifiedProcess V α β 0) 1 μ := by
  have h_supermartingale : Supermartingale (modifiedProcess V α β) ℱ μ := by
    apply_rules [ modifiedProcess_supermartingale ];
  have h_integral_le : ∫ ω, (modifiedProcess V α β n) ω ∂μ ≤ ∫ ω, (modifiedProcess V α β 0) ω ∂μ := by
    have := h_supermartingale.2;
    have := this.1 0 n (Nat.zero_le n);
    convert MeasureTheory.integral_mono_ae _ _ this using 1;
    · rw [ MeasureTheory.integral_condExp ];
    · exact MeasureTheory.integrable_condExp;
    · aesop;
  have h_integral_le : ∫⁻ ω, ENNReal.ofReal (modifiedProcess V α β n ω) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (modifiedProcess V α β 0 ω) ∂μ := by
    convert ENNReal.ofReal_le_ofReal h_integral_le using 1;
    · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · exact?;
      · exact modifiedProcess_nonneg hV_nn hα_nn hβ_nn n;
    · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · exact?;
      · exact modifiedProcess_nonneg hV_nn hα_nn hβ_nn 0;
  convert h_integral_le using 1 <;> rw [ eLpNorm_one_eq_lintegral_enorm ];
  · refine' MeasureTheory.lintegral_congr_ae _;
    filter_upwards [ modifiedProcess_nonneg hV_nn hα_nn hβ_nn n ] with ω hω using by rw [ Real.enorm_eq_ofReal hω ] ;
  · have h_nonneg : 0 ≤ᵐ[μ] modifiedProcess V α β 0 := by
      exact modifiedProcess_nonneg hV_nn hα_nn hβ_nn 0;
    exact MeasureTheory.lintegral_congr_ae ( by filter_upwards [ h_nonneg ] with ω hω using by rw [ Real.enorm_eq_ofReal hω ] )

/-! ### Main theorem -/

/-
**Robbins–Siegmund almost-supermartingale convergence lemma.**
-/
theorem robbins_siegmund [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (V : ℕ → Ω → ℝ) (α β : ℕ → ℝ)
    (hV_adapt : ∀ n, StronglyMeasurable[ℱ n] (V n))
    (hV_nn : ∀ n, 0 ≤ᵐ[μ] V n)
    (hV_int : ∀ n, Integrable (V n) μ)
    (hα_nn : ∀ n, 0 ≤ α n)
    (hα_sum : Summable α)
    (hβ_nn : ∀ n, 0 ≤ β n)
    (hβ_sum : Summable β)
    (h_cond : ∀ n,
      μ[V (n + 1)|ℱ n] ≤ᵐ[μ] fun ω => (1 + α n) * V n ω + β n) :
    ∃ V_inf : Ω → ℝ,
      ∀ᵐ ω ∂μ, Tendsto (fun n => V n ω) atTop (𝓝 (V_inf ω)) := by
  -- By the supermartingale convergence theorem, the modified process $S_n$ converges almost surely to some limit $S_\infty$.
  obtain ⟨S_inf, hS_inf⟩ : ∃ S_inf : Ω → ℝ, ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => modifiedProcess V α β n ω) Filter.atTop (nhds (S_inf ω)) := by
    have h_supermartingale : Supermartingale (modifiedProcess V α β) ℱ μ := by
      apply_rules [ modifiedProcess_supermartingale ];
    have h_bounded : ∀ n, eLpNorm (modifiedProcess V α β n) 1 μ ≤ eLpNorm (modifiedProcess V α β 0) 1 μ := by
      apply_rules [ modifiedProcess_eLpNorm_bound ];
    have := @Submartingale.ae_tendsto_limitProcess;
    specialize this ( show Submartingale ( fun n ω => -modifiedProcess V α β n ω ) ℱ μ from ?_ ) ?_;
    exact ENNReal.toNNReal ( eLpNorm ( modifiedProcess V α β 0 ) 1 μ );
    · convert h_supermartingale.neg using 1;
    · simp_all +decide [ eLpNorm_one_eq_lintegral_enorm ];
      rw [ ENNReal.coe_toNNReal ];
      · exact h_bounded;
      · refine' ne_of_lt ( MeasureTheory.Integrable.hasFiniteIntegral _ );
        exact?;
    · exact ⟨ fun ω => -Filtration.limitProcess ( fun n ω => -modifiedProcess V α β n ω ) ℱ μ ω, by filter_upwards [ this ] with ω hω using by simpa using hω.neg ⟩;
  obtain ⟨P_inf, hP_inf⟩ : ∃ P_inf : ℝ, 0 < P_inf ∧ Filter.Tendsto (partialProd α) Filter.atTop (nhds P_inf) := by
    exact?;
  -- By definition of $V$, we have $V_n = P_n S_n - R_n$.
  have hV_def : ∀ᵐ ω ∂μ, ∀ n, V n ω = partialProd α n * modifiedProcess V α β n ω - tailSum β n := by
    simp +decide [ modifiedProcess, mul_div_cancel₀ _ ( ne_of_gt ( partialProd_pos hα_nn _ ) ) ];
  use fun ω => P_inf * S_inf ω - 0;
  filter_upwards [ hV_def, hS_inf ] with ω hω₁ hω₂;
  simpa only [ hω₁ ] using Filter.Tendsto.sub ( hP_inf.2.mul hω₂ ) ( tailSum_tendsto_zero hβ_sum )

end

end Pythia.StochasticApproximation