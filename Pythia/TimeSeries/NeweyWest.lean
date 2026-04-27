/-
Copyright (c) 2024 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Newey-West HAC Variance Estimator — IID Special Case

We formalize the consistency of the Bartlett-kernel HAC (Heteroskedasticity and
Autocorrelation Consistent) variance estimator of Newey & West (1987,
*Econometrica* 55:703–708) in the iid special case.

## Setting

Given an iid sequence `{X_t}` with `E[X_t] = 0` and `E[X_t²] = σ²`, the
Newey-West estimator is

  `Σ̂_T = γ̂(0) + 2 ∑_{j=1}^{m(T)} (1 - j/(m(T)+1)) γ̂(j)`

where `γ̂(j) = (1/T) ∑_{t=j}^{T-1} X_t X_{t-j}` is the sample autocovariance
at lag `j`, and `m(T)` is a bandwidth parameter.

## Main result

* `NeweyWest.hac_consistent` — Under iid with finite fourth moment, if the
  bandwidth satisfies `m(T) → ∞` and `m(T) / T^{1/4} → 0`, then `Σ̂_T →_p σ²`.

In the iid case all population autocovariances at lag ≥ 1 vanish, so the
estimator reduces to `γ̂(0)` plus a remainder that vanishes in probability.
The proof decomposes into:
1. `gammaHat_zero_tendsto` — `γ̂(0) →_p σ²` via the WLLN.
2. `bartlett_remainder_tendsto` — the weighted sum of sample autocovariances
   at positive lags vanishes in probability.

## Future work (Tier 3)

The general mixing-process version under α-mixing or β-mixing conditions,
which is the main content of Newey-West (1987), is left for future work.

## References

* Newey, W.K. and West, K.D. (1987). *A Simple, Positive Semi-definite,
  Heteroskedasticity and Autocorrelation Consistent Covariance Matrix*.
  Econometrica 55(3):703–708.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

namespace Pythia.TimeSeries.NeweyWest

/-! ### Definitions -/

/-- Bartlett kernel weight: `w(j, m) = 1 - j / (m + 1)` for `j ≤ m`, and `0` otherwise. -/
def bartlettWeight (j m : ℕ) : ℝ :=
  if j ≤ m then 1 - (j : ℝ) / ((m : ℝ) + 1) else 0

/-- Sample autocovariance at lag `j` for a sequence `X : ℕ → Ω → ℝ` with sample size `T`:
  `γ̂(j) = (1/T) ∑_{t=j}^{T-1} X_t · X_{t-j}`. -/
def sampleAutocovariance {Ω : Type*} (X : ℕ → Ω → ℝ) (T j : ℕ) (ω : Ω) : ℝ :=
  if T = 0 then 0
  else (1 / (T : ℝ)) * ∑ t ∈ Finset.Ico j T, X t ω * X (t - j) ω

/-- Newey-West HAC estimator with Bartlett kernel and bandwidth `m`:
  `Σ̂(T, m) = γ̂(0) + 2 ∑_{j=1}^{m} w(j, m) · γ̂(j)`. -/
def hacEstimator {Ω : Type*} (X : ℕ → Ω → ℝ) (T m : ℕ) (ω : Ω) : ℝ :=
  sampleAutocovariance X T 0 ω +
    2 * ∑ j ∈ Finset.Icc 1 m, bartlettWeight j m * sampleAutocovariance X T j ω

/-! ### Bartlett weight properties -/

lemma bartlettWeight_nonneg (j m : ℕ) : 0 ≤ bartlettWeight j m := by
  unfold bartlettWeight
  split_ifs <;> first
    | positivity
    | exact sub_nonneg.2 <| div_le_one_of_le₀ (by norm_cast; linarith) (by positivity)

lemma bartlettWeight_le_one (j m : ℕ) : bartlettWeight j m ≤ 1 := by
  unfold bartlettWeight
  split_ifs <;> [exact sub_le_self _ (by positivity); norm_num]

lemma bartlettWeight_zero (m : ℕ) : bartlettWeight 0 m = 1 := by
  unfold bartlettWeight; aesop

lemma bartlettWeight_eq_zero_of_gt {j m : ℕ} (h : m < j) : bartlettWeight j m = 0 := by
  unfold bartlettWeight; aesop

/-! ### Main theorem setup -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The remainder term in the Newey-West estimator: the weighted sum of sample
autocovariances at positive lags. -/
def hacRemainder {Ω : Type*} (X : ℕ → Ω → ℝ) (T m : ℕ) (ω : Ω) : ℝ :=
  2 * ∑ j ∈ Finset.Icc 1 m, bartlettWeight j m * sampleAutocovariance X T j ω

/-- The HAC estimator decomposes as γ̂(0) + remainder. -/
lemma hacEstimator_eq_gamma_zero_add_remainder {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T m : ℕ) (ω : Ω) :
    hacEstimator X T m ω = sampleAutocovariance X T 0 ω + hacRemainder X T m ω := by
  simp only [hacEstimator, hacRemainder]

/-! ### Convergence of the lag-0 sample autocovariance -/

set_option maxHeartbeats 400000 in
theorem gammaHat_zero_tendsto
    (X : ℕ → Ω → ℝ) (σ_sq : ℝ) (hσ_sq_nonneg : 0 ≤ σ_sq)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_indep : iIndepFun (m := fun (_ : ℕ) => inferInstance) X μ)
    (hX_ident : ∀ t, IdentDistrib (X t) (X 0) μ μ)
    (hX_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hX_var : ∫ ω, X 0 ω ^ 2 ∂μ = σ_sq)
    (hX_int_sq : Integrable (fun ω => X 0 ω ^ 2) μ) :
    TendstoInMeasure μ
      (fun T ω => sampleAutocovariance X T 0 ω) atTop (fun _ => σ_sq) := by
  have h_slln : ∀ᵐ ω ∂μ, Filter.Tendsto (fun T => (∑ t ∈ Finset.range T, X t ω ^ 2) / T) Filter.atTop (nhds (∫ ω, X 0 ω ^ 2 ∂μ)) := by
    have := @ProbabilityTheory.strong_law_ae_real;
    specialize this ( fun t ω => X t ω ^ 2 ) hX_int_sq ( fun i j hij => ?_ ) ( fun t => ?_ );
    · have := hX_indep.indepFun hij;
      exact this.comp ( measurable_id.pow_const 2 ) ( measurable_id.pow_const 2 );
    · exact IdentDistrib.comp ( hX_ident t ) ( measurable_id.pow_const 2 );
    · exact this;
  have h_slln : TendstoInMeasure μ (fun T ω => (∑ t ∈ Finset.range T, X t ω ^ 2) / T) Filter.atTop (fun _ => ∫ ω, X 0 ω ^ 2 ∂μ) := by
    apply_rules [ tendstoInMeasure_of_tendsto_ae ];
    exact fun n => Measurable.aestronglyMeasurable ( by measurability );
  convert h_slln using 1;
  · ext T ω; unfold sampleAutocovariance; by_cases hT : T = 0 <;> simp +decide [ hT, div_eq_inv_mul, Finset.sum_range, pow_two ] ;
  · aesop

/-! ### Helper lemmas for the remainder convergence -/

/-
For iid `X_t` with `E[X_t] = 0` and `E[X_t⁴] < ∞`, the second moment
of the sample autocovariance at lag `j ≥ 1` satisfies
`E[γ̂(j)²] ≤ E[X₀⁴] / T`. This follows because:
- `γ̂(j) = (1/T) ∑_{t=j}^{T-1} X_t X_{t-j}`
- The products `X_t X_{t-j}` for distinct `t` are independent mean-zero
  random variables (by iid with mean 0).
- `Var(X_t X_{t-j}) = E[(X_t X_{t-j})²] ≤ E[X₀⁴]` by iid and Cauchy-Schwarz.
- Therefore `E[γ̂(j)²] = Var(γ̂(j)) ≤ (T-j)/(T²) E[X₀⁴] ≤ E[X₀⁴]/T`.
-/
set_option maxHeartbeats 800000 in
theorem gammaHat_lag_second_moment_bound
    (X : ℕ → Ω → ℝ) (T : ℕ) (j : ℕ) (hj : 1 ≤ j) (hT : 1 ≤ T)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_indep : iIndepFun (m := fun (_ : ℕ) => inferInstance) X μ)
    (hX_ident : ∀ t, IdentDistrib (X t) (X 0) μ μ)
    (hX_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hX_fourth : Integrable (fun ω => X 0 ω ^ 4) μ) :
    ∫ ω, (sampleAutocovariance X T j ω) ^ 2 ∂μ ≤
      (∫ ω, X 0 ω ^ 4 ∂μ) / T := by
  -- By definition of $sampleAutocovariance$, we can expand its square.
  have h_expand : ∫ ω, (sampleAutocovariance X T j ω) ^ 2 ∂μ = (1 / (T : ℝ)) ^ 2 * ∑ s ∈ Finset.Ico j T, ∑ t ∈ Finset.Ico j T, ∫ ω, X s ω * X (s - j) ω * X t ω * X (t - j) ω ∂μ := by
    rw [ ← Finset.sum_product' ];
    rw [ ← MeasureTheory.integral_finset_sum ];
    · rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ω ; unfold sampleAutocovariance ; by_cases h : T = 0 <;> simp +decide [ *, Finset.sum_mul _ _ _ ] ; ring;
      simp +decide only [sq, sum_mul_sum, mul_assoc, sum_product];
    · intro i hi
      have h_integrable : ∀ t, Integrable (fun ω => X t ω ^ 4) μ := by
        intro t;
        have := hX_ident t;
        exact this.comp ( measurable_id.pow_const 4 ) |> fun h => h.integrable_iff.mpr hX_fourth;
      refine' MeasureTheory.Integrable.mono' ( h_integrable i.1 |> fun h => h.add ( h_integrable ( i.1 - j ) ) |> fun h => h.add ( h_integrable i.2 ) |> fun h => h.add ( h_integrable ( i.2 - j ) ) ) _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( hX_meas _ |> Measurable.aestronglyMeasurable ) ( hX_meas _ |> Measurable.aestronglyMeasurable ) ) ( hX_meas _ |> Measurable.aestronglyMeasurable ) ) ( hX_meas _ |> Measurable.aestronglyMeasurable );
      · filter_upwards [ ] with ω;
        norm_num;
        rw [ ← abs_mul, ← abs_mul, ← abs_mul ];
        rw [ abs_le ];
        constructor <;> nlinarith only [ sq_nonneg ( X i.1 ω * X ( i.1 - j ) ω - X i.2 ω * X ( i.2 - j ) ω ), sq_nonneg ( X i.1 ω * X ( i.1 - j ) ω + X i.2 ω * X ( i.2 - j ) ω ), sq_nonneg ( X i.1 ω ^ 2 - X ( i.1 - j ) ω ^ 2 ), sq_nonneg ( X i.2 ω ^ 2 - X ( i.2 - j ) ω ^ 2 ) ];
  -- By independence and identical distribution, we have $\mathbb{E}[X_s X_{s-j} X_t X_{t-j}] = \mathbb{E}[X_0^2]^2$ if $s = t$ and $s - j = t - j$, and $0$ otherwise.
  have h_indep : ∀ s t, s ∈ Finset.Ico j T → t ∈ Finset.Ico j T → s ≠ t ∨ s - j ≠ t - j → ∫ ω, X s ω * X (s - j) ω * X t ω * X (t - j) ω ∂μ = 0 := by
    intro s t hs ht hst
    have h_indep : ∀ (a b c d : ℕ), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → ∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ = (∫ ω, X a ω ∂μ) * (∫ ω, X b ω ∂μ) * (∫ ω, X c ω ∂μ) * (∫ ω, X d ω ∂μ) := by
      intros a b c d hab hbc hcd hca hcb hcd'
      have h_indep : ProbabilityTheory.IndepFun (fun ω => X a ω) (fun ω => X b ω * X c ω * X d ω) μ := by
        have := hX_indep.indepFun_finset { a } { b, c, d } ; simp_all +decide [ Set.disjoint_left ] ;
        rw [ ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul ] at *;
        intro s t hs ht; specialize this ( ( fun f => f ⟨ a, by simp +decide ⟩ ) ⁻¹' s ) ( ( fun f => f ⟨ b, by simp +decide ⟩ * f ⟨ c, by simp +decide ⟩ * f ⟨ d, by simp +decide ⟩ ) ⁻¹' t ) ; simp_all +decide [ Set.preimage ] ;
        apply this;
        · exact measurableSet_preimage ( measurable_pi_apply _ ) hs |> MeasurableSet.mem;
        · exact MeasurableSet.mem ( ht.preimage ( Measurable.mul ( Measurable.mul ( measurable_pi_apply _ ) ( measurable_pi_apply _ ) ) ( measurable_pi_apply _ ) ) );
      have h_indep : ∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ = (∫ ω, X a ω ∂μ) * (∫ ω, X b ω * X c ω * X d ω ∂μ) := by
        rw [ ← ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
        · simp +decide [ mul_assoc ];
        · exact h_indep;
        · exact hX_meas a |> Measurable.aestronglyMeasurable;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( hX_meas b |> Measurable.aestronglyMeasurable ) ( hX_meas c |> Measurable.aestronglyMeasurable ) ) ( hX_meas d |> Measurable.aestronglyMeasurable );
      aesop;
    by_cases h_cases : s = t ∨ s = t - j ∨ s - j = t ∨ s - j = t - j;
    · rcases h_cases with ( rfl | rfl | h_cases | h_cases ) <;> simp_all +decide;
      · have h_indep : ∫ ω, X (t - j) ω ^ 2 * X (t - j - j) ω * X t ω ∂μ = (∫ ω, X (t - j) ω ^ 2 ∂μ) * (∫ ω, X (t - j - j) ω * X t ω ∂μ) := by
          rw [ ← ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
          · simp +decide only [mul_assoc, Pi.mul_apply];
          · have h_indep : ProbabilityTheory.IndepFun (fun ω => X (t - j) ω) (fun ω => X (t - j - j) ω * X t ω) μ := by
              have h_indep : ProbabilityTheory.IndepFun (fun ω => X (t - j) ω) (fun ω => (X (t - j - j) ω, X t ω)) μ := by
                have := hX_indep.indepFun_finset { t - j } { t - j - j, t } ; simp_all +decide [ Set.Pairwise ] ;
                specialize this ( by omega ) ( by omega );
                convert this.comp _ _ using 1;
                congr! 1;
                rotate_left;
                rotate_left;
                use fun f => f ⟨ t - j, by simp +decide ⟩;
                use fun f => ( f ⟨ t - j - j, by simp +decide ⟩, f ⟨ t, by simp +decide ⟩ );
                · exact measurable_pi_apply _;
                · exact measurable_pi_apply _ |> Measurable.prodMk <| measurable_pi_apply _;
                · exact funext fun ω => rfl;
                · exact funext fun ω => rfl;
              convert h_indep.comp ( measurable_id' ) ( measurable_fst.mul measurable_snd ) using 1;
            exact h_indep.comp ( measurable_id'.pow_const 2 ) measurable_id';
          · exact MeasureTheory.AEStronglyMeasurable.pow ( hX_meas _ |> Measurable.aestronglyMeasurable ) _;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( hX_meas _ |> Measurable.aestronglyMeasurable ) ( hX_meas _ |> Measurable.aestronglyMeasurable );
        convert h_indep using 1;
        · exact congr_arg _ ( funext fun ω => by ring );
        · have h_indep : ∫ ω, X (t - j - j) ω * X t ω ∂μ = (∫ ω, X (t - j - j) ω ∂μ) * (∫ ω, X t ω ∂μ) := by
            apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
            · exact hX_indep.indepFun ( by omega );
            · exact hX_meas _ |> Measurable.aestronglyMeasurable;
            · exact hX_meas t |> Measurable.aestronglyMeasurable;
          aesop;
      · have h_indep : ∫ ω, X (t + j) ω * X t ω * X t ω * X (t - j) ω ∂μ = (∫ ω, X (t + j) ω ∂μ) * (∫ ω, X t ω * X t ω * X (t - j) ω ∂μ) := by
          rw [ ← ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
          · simp +decide [ mul_assoc ];
          · have := hX_indep.indepFun_finset { t + j } { t, t - j } ; simp_all +decide [ Set.Pairwise ] ;
            specialize this ( by linarith ) ( by omega );
            convert this.comp _ _ using 1;
            congr! 1;
            rotate_left;
            rotate_left;
            use fun f => f ⟨ t + j, by simp +decide ⟩;
            use fun f => f ⟨ t, by simp +decide ⟩ * f ⟨ t, by simp +decide ⟩ * f ⟨ t - j, by simp +decide ⟩;
            · exact measurable_pi_apply _;
            · fun_prop;
            · exact funext fun _ => rfl;
            · exact funext fun ω => rfl;
          · exact hX_meas _ |> Measurable.aestronglyMeasurable;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( hX_meas t |> Measurable.aestronglyMeasurable ) ( hX_meas t |> Measurable.aestronglyMeasurable ) ) ( hX_meas ( t - j ) |> Measurable.aestronglyMeasurable );
        aesop;
      · omega;
    · simp_all +decide [ mul_assoc ];
      exact h_indep _ _ _ _ ( by omega ) ( by omega ) ( by omega ) ( by omega ) ( by omega ) ( by omega );
  -- By independence and identical distribution, we have $\mathbb{E}[X_s X_{s-j} X_t X_{t-j}] = \mathbb{E}[X_0^2]^2$ if $s = t$ and $s - j = t - j$.
  have h_indep_eq : ∀ s ∈ Finset.Ico j T, ∫ ω, X s ω * X (s - j) ω * X s ω * X (s - j) ω ∂μ ≤ ∫ ω, X 0 ω ^ 4 ∂μ := by
    intro s hs
    have h_indep_eq : ∫ ω, X s ω ^ 2 * X (s - j) ω ^ 2 ∂μ ≤ ∫ ω, X s ω ^ 4 ∂μ := by
      have h_indep_eq : ∫ ω, X s ω ^ 2 * X (s - j) ω ^ 2 ∂μ ≤ ∫ ω, (X s ω ^ 4 + X (s - j) ω ^ 4) / 2 ∂μ := by
        refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
        · exact Filter.Eventually.of_forall fun ω => mul_nonneg ( sq_nonneg _ ) ( sq_nonneg _ );
        · refine' MeasureTheory.Integrable.div_const _ _;
          refine' MeasureTheory.Integrable.add _ _;
          · have := hX_ident s;
            exact this.comp ( measurable_id.pow_const 4 ) |> fun h => h.integrable_iff.mpr hX_fourth;
          · have := hX_ident ( s - j );
            exact this.comp ( measurable_id.pow_const 4 ) |> fun h => h.integrable_iff.mpr hX_fourth;
        · filter_upwards [ ] with ω using by nlinarith only [ sq_nonneg ( X s ω ^ 2 - X ( s - j ) ω ^ 2 ) ] ;
      rw [ MeasureTheory.integral_div, MeasureTheory.integral_add ] at h_indep_eq;
      · have h_indep_eq : ∫ ω, X s ω ^ 4 ∂μ = ∫ ω, X 0 ω ^ 4 ∂μ ∧ ∫ ω, X (s - j) ω ^ 4 ∂μ = ∫ ω, X 0 ω ^ 4 ∂μ := by
          exact ⟨ by simpa using hX_ident s |> fun h => h.comp ( measurable_id.pow_const 4 ) |> fun h => h.integral_eq, by simpa using hX_ident ( s - j ) |> fun h => h.comp ( measurable_id.pow_const 4 ) |> fun h => h.integral_eq ⟩;
        linarith;
      · have := hX_ident s;
        exact this.comp ( measurable_id.pow_const 4 ) |> fun h => h.integrable_iff.mpr hX_fourth;
      · have := hX_ident ( s - j );
        exact this.comp ( measurable_id.pow_const 4 ) |> IdentDistrib.integrable_iff |>.2 hX_fourth;
    convert h_indep_eq using 1;
    · exact congr_arg _ ( funext fun ω => by ring );
    · exact ( hX_ident s |> IdentDistrib.pow |> IdentDistrib.comp <| measurable_id ) |> IdentDistrib.integral_eq |> Eq.symm;
  -- Apply the independence and identical distribution results to simplify the double sum.
  have h_double_sum : ∑ s ∈ Finset.Ico j T, ∑ t ∈ Finset.Ico j T, ∫ ω, X s ω * X (s - j) ω * X t ω * X (t - j) ω ∂μ ≤ ∑ s ∈ Finset.Ico j T, ∫ ω, X 0 ω ^ 4 ∂μ := by
    refine' Finset.sum_le_sum fun s hs => _;
    rw [ Finset.sum_eq_single s ];
    · exact h_indep_eq s hs;
    · exact fun t ht hts => h_indep s t hs ht ( by tauto );
    · aesop;
  simp_all +decide [ div_eq_inv_mul ];
  field_simp;
  exact h_double_sum.trans ( mul_le_mul_of_nonneg_right ( mod_cast Nat.sub_le _ _ ) ( MeasureTheory.integral_nonneg fun _ => by positivity ) )

/-
The squared L² norm of the Bartlett-kernel remainder is bounded by
`4 m² E[X₀⁴] / T`. This follows from Cauchy-Schwarz on the finite sum:
`(∑ w_j γ̂(j))² ≤ m ∑ γ̂(j)²` (since `|w_j| ≤ 1`), hence
`E[remainder²] = 4 E[(∑ w_j γ̂(j))²] ≤ 4 m ∑ E[γ̂(j)²] ≤ 4m² E[X₀⁴]/T`.
-/
theorem hacRemainder_second_moment_bound
    (X : ℕ → Ω → ℝ) (T m : ℕ) (hT : 1 ≤ T)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_indep : iIndepFun (m := fun (_ : ℕ) => inferInstance) X μ)
    (hX_ident : ∀ t, IdentDistrib (X t) (X 0) μ μ)
    (hX_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hX_fourth : Integrable (fun ω => X 0 ω ^ 4) μ) :
    ∫ ω, (hacRemainder X T m ω) ^ 2 ∂μ ≤
      4 * (m : ℝ) ^ 2 * (∫ ω, X 0 ω ^ 4 ∂μ) / T := by
  have h_remainder_bound : ∫ ω, (hacRemainder X T m ω) ^ 2 ∂μ ≤ 4 * m * ∑ j ∈ Finset.Icc 1 m, ∫ ω, (sampleAutocovariance X T j ω) ^ 2 ∂μ := by
    unfold hacRemainder;
    -- Apply the Cauchy-Schwarz inequality to the sum.
    have h_cauchy_schwarz : ∀ ω, (∑ j ∈ Finset.Icc 1 m, bartlettWeight j m * sampleAutocovariance X T j ω) ^ 2 ≤ m * ∑ j ∈ Finset.Icc 1 m, (sampleAutocovariance X T j ω) ^ 2 := by
      intro ω
      have h_cauchy_schwarz : (∑ j ∈ Finset.Icc 1 m, bartlettWeight j m * sampleAutocovariance X T j ω) ^ 2 ≤ (∑ j ∈ Finset.Icc 1 m, (bartlettWeight j m) ^ 2) * (∑ j ∈ Finset.Icc 1 m, (sampleAutocovariance X T j ω) ^ 2) := by
        exact sum_mul_sq_le_sq_mul_sq (Icc 1 m) _ _;
      refine' le_trans h_cauchy_schwarz ( mul_le_mul_of_nonneg_right _ <| Finset.sum_nonneg fun _ _ => sq_nonneg _ );
      exact le_trans ( Finset.sum_le_sum fun _ _ => pow_le_one₀ ( bartlettWeight_nonneg _ _ ) ( bartlettWeight_le_one _ _ ) ) ( by norm_num );
    by_cases h_integrable : ∀ j ∈ Finset.Icc 1 m, MeasureTheory.Integrable (fun ω => (sampleAutocovariance X T j ω) ^ 2) μ;
    · have h_integral_cauchy_schwarz : ∫ ω, (∑ j ∈ Finset.Icc 1 m, bartlettWeight j m * sampleAutocovariance X T j ω) ^ 2 ∂μ ≤ m * ∑ j ∈ Finset.Icc 1 m, ∫ ω, (sampleAutocovariance X T j ω) ^ 2 ∂μ := by
        refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
        refine' fun ω => m * ∑ j ∈ Finset.Icc 1 m, sampleAutocovariance X T j ω ^ 2;
        · exact Filter.Eventually.of_forall fun ω => sq_nonneg _;
        · exact MeasureTheory.Integrable.const_mul ( MeasureTheory.integrable_finset_sum _ h_integrable ) _;
        · filter_upwards [ ] using h_cauchy_schwarz;
        · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _ fun j hj => h_integrable j hj ];
      norm_num [ mul_pow, MeasureTheory.integral_const_mul ] at * ; linarith;
    · contrapose! h_integrable;
      intro j hj;
      refine' MeasureTheory.MemLp.integrable_sq _;
      have h_integrable : ∀ t, MeasureTheory.Integrable (fun ω => X t ω ^ 2) μ := by
        intro t;
        have := hX_ident t;
        have := this.comp ( measurable_id.pow_const 2 );
        have := this.integrable_iff;
        refine' this.mpr _;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        exact fun ω => X 0 ω ^ 4 + 1;
        · exact MeasureTheory.Integrable.add hX_fourth ( MeasureTheory.integrable_const _ );
        · exact MeasureTheory.AEStronglyMeasurable.pow ( hX_meas 0 |> Measurable.aestronglyMeasurable ) _;
        · filter_upwards [ ] with ω using by norm_num; nlinarith only [ sq_nonneg ( X 0 ω ^ 2 - 1 ) ] ;
      refine' MemLp.mono' _ _ _;
      refine' fun ω => ( 1 / T ) * ∑ t ∈ Finset.Ico j T, ( X t ω ^ 2 + X ( t - j ) ω ^ 2 );
      · refine' MemLp.const_mul _ _;
        refine' MeasureTheory.memLp_finset_sum _ fun t ht => _;
        refine' MemLp.add _ _;
        · rw [ memLp_two_iff_integrable_sq ];
          · have := hX_ident t;
            have := this.comp ( measurable_id.pow_const 4 );
            convert this.integrable_iff.mpr hX_fourth using 1 ; ext ; norm_num ; ring;
          · exact MeasureTheory.Integrable.aestronglyMeasurable ( h_integrable t );
        · rw [ memLp_two_iff_integrable_sq ];
          · have := hX_ident ( t - j );
            have := this.comp ( measurable_id'.pow_const 4 );
            convert this.integrable_iff.mpr hX_fourth using 1 ; ext ; ring;
            norm_cast;
          · exact MeasureTheory.Integrable.aestronglyMeasurable ( h_integrable _ );
      · refine' Measurable.aestronglyMeasurable _;
        exact Measurable.ite ( by norm_num ) measurable_const ( Measurable.mul measurable_const ( Finset.measurable_sum _ fun t ht => Measurable.mul ( hX_meas t ) ( hX_meas ( t - j ) ) ) );
      · filter_upwards [ ] with ω;
        unfold sampleAutocovariance;
        split_ifs <;> norm_num;
        · linarith;
        · exact mul_le_mul_of_nonneg_left ( le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun _ _ => by rw [ abs_le ] ; constructor <;> nlinarith only [ sq_nonneg ( X ‹_› ω - X ( ‹_› - j ) ω ), sq_nonneg ( X ‹_› ω + X ( ‹_› - j ) ω ) ] ) ) ( by positivity );
  have h_sum_bound : ∑ j ∈ Finset.Icc 1 m, ∫ ω, (sampleAutocovariance X T j ω) ^ 2 ∂μ ≤ m * (∫ ω, X 0 ω ^ 4 ∂μ) / T := by
    convert Finset.sum_le_sum fun j hj => gammaHat_lag_second_moment_bound X T j ( Finset.mem_Icc.mp hj |>.1 ) hT hX_meas hX_indep hX_ident hX_mean hX_fourth using 1 ; norm_num ; ring;
  exact h_remainder_bound.trans ( by convert mul_le_mul_of_nonneg_left h_sum_bound ( show ( 0 : ℝ ) ≤ 4 * m by positivity ) using 1 ; ring )

/-
Chebyshev bound: if `E[f²] ≤ B` and `B → 0`, then `f →_p 0`.
-/
theorem tendstoInMeasure_of_second_moment_tendsto
    {f : ℕ → Ω → ℝ} {B : ℕ → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hf_int : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ)
    (hf_bound : ∀ n, ∫ ω, (f n ω) ^ 2 ∂μ ≤ B n)
    (hB_nonneg : ∀ n, 0 ≤ B n)
    (hB_tendsto : Tendsto B atTop (nhds 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  intro ε hε;
  rcases eq_or_ne ε ⊤ with rfl | hε' <;> simp_all +decide [ edist_dist ];
  -- By the properties of the measure, we can bound the measure of the set where $|f_n(x)| \geq \epsilon$.
  have h_measure_bound : ∀ n, μ {x | ε ≤ ENNReal.ofReal |f n x|} ≤ ENNReal.ofReal ((∫ ω, f n ω ^ 2 ∂μ) / (ε.toReal ^ 2)) := by
    intro n
    have h_measure_bound : μ {x | ε ≤ ENNReal.ofReal |f n x|} ≤ μ {x | ε.toReal ^ 2 ≤ |f n x| ^ 2} := by
      refine' MeasureTheory.measure_mono _;
      intro x hx; exact pow_le_pow_left₀ ( ENNReal.toReal_nonneg ) ( by simpa [ ← ENNReal.toReal_le_toReal, hε', hx.out ] using ENNReal.toReal_mono ( by aesop ) hx.out ) 2;
    have h_measure_bound : μ {x | ε.toReal ^ 2 ≤ |f n x| ^ 2} ≤ ENNReal.ofReal ((∫ ω, |f n ω| ^ 2 ∂μ) / (ε.toReal ^ 2)) := by
      have := @MeasureTheory.mul_meas_ge_le_integral_of_nonneg Ω _ μ ( fun ω => |f n ω| ^ 2 );
      specialize this ( Filter.Eventually.of_forall fun ω => sq_nonneg _ ) ( by simpa using hf_int n ) ( ε.toReal ^ 2 );
      rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num;
      · rw [ le_div_iff₀' ( sq_pos_of_pos ( ENNReal.toReal_pos hε.ne' hε' ) ) ] ; aesop;
      · finiteness;
    exact le_trans ‹_› ( h_measure_bound.trans_eq ( by simp +decide [ abs_mul, sq_abs ] ) );
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ ( fun n => zero_le _ ) ( fun n => h_measure_bound n );
  simpa using ENNReal.tendsto_ofReal ( Filter.Tendsto.div_const ( squeeze_zero ( fun _ => MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ) hf_bound hB_tendsto ) _ )

/-
From `m(T)/T^{1/4} → 0` we deduce `m(T)²/(T+1) → 0`.
-/
theorem bandwidth_rate_sq_tendsto (m : ℕ → ℕ)
    (hm_rate : Tendsto (fun T => (m T : ℝ) / (T : ℝ) ^ (1/4 : ℝ)) atTop (nhds 0)) :
    Tendsto (fun T => (m T : ℝ) ^ 2 / ((T : ℝ) + 1)) atTop (nhds 0) := by
  -- We can bound the expression as follows:
  have h_bound : ∀ T : ℕ, T ≥ 1 → (m T : ℝ) ^ 2 / (T + 1) ≤ (m T / (T : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / (T : ℝ) ^ (1 / 2 : ℝ) := by
    intro T hT; rw [ div_pow ] ; rw [ div_div ] ; rw [ div_le_div_iff₀ ] <;> try positivity;
    norm_num [ sq, ← Real.rpow_add ( by positivity : 0 < ( T : ℝ ) ) ];
    exact mul_le_mul_of_nonneg_left ( by linarith ) ( by positivity );
  refine' squeeze_zero_norm' _ _;
  exacts [ fun T => ( m T / T ^ ( 1 / 4 : ℝ ) ) ^ 2 / T ^ ( 1 / 2 : ℝ ), Filter.eventually_atTop.mpr ⟨ 1, fun T hT => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound T hT ⟩, by simpa using Filter.Tendsto.div_atTop ( hm_rate.pow 2 ) ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ]

/-! ### Convergence of the Bartlett-kernel remainder -/

/-
For iid `X_t` with `E[X_t⁴] < ∞`, and bandwidth `m(T) → ∞` with
`m(T) / T^{1/4} → 0`, the Bartlett-kernel remainder vanishes in probability.
-/
theorem bartlett_remainder_tendsto
    (X : ℕ → Ω → ℝ) (m : ℕ → ℕ)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_indep : iIndepFun (m := fun (_ : ℕ) => inferInstance) X μ)
    (hX_ident : ∀ t, IdentDistrib (X t) (X 0) μ μ)
    (hX_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hX_int_sq : Integrable (fun ω => X 0 ω ^ 2) μ)
    (hX_fourth : Integrable (fun ω => X 0 ω ^ 4) μ)
    (hm_tendsto : Tendsto (fun T => (m T : ℝ)) atTop atTop)
    (hm_rate : Tendsto (fun T => (m T : ℝ) / (T : ℝ) ^ (1/4 : ℝ)) atTop (nhds 0)) :
    TendstoInMeasure μ
      (fun T ω => hacRemainder X (T + 1) (m T) ω) atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_second_moment_tendsto;
  any_goals intro n; exact hacRemainder_second_moment_bound X ( n + 1 ) ( m n ) ( by linarith ) hX_meas hX_indep hX_ident hX_mean hX_fourth;
  · intro n;
    refine' Measurable.aestronglyMeasurable _;
    refine' Measurable.const_mul _ _;
    refine' Finset.measurable_sum _ fun j hj => Measurable.mul _ _;
    · exact measurable_const;
    · exact Measurable.const_mul ( Finset.measurable_sum _ fun t ht => Measurable.mul ( hX_meas t ) ( hX_meas ( t - j ) ) ) _;
  · intro n
    have h_integrable : ∀ j, Integrable (fun ω => (sampleAutocovariance X (n + 1) j ω) ^ 2) μ := by
      intro j
      simp [sampleAutocovariance];
      simp +decide [Finset.mul_sum _ _ _ ];
      refine' MeasureTheory.MemLp.integrable_sq _;
      refine' MeasureTheory.memLp_finset_sum _ fun i hi => _;
      refine' MemLp.const_mul _ _;
      refine' MemLp.mono' _ _ _;
      exact fun ω => X i ω ^ 2 + X ( i - j ) ω ^ 2;
      · refine' MemLp.add _ _;
        · rw [ memLp_two_iff_integrable_sq ];
          · have := hX_ident i;
            have := this.comp ( show Measurable fun x : ℝ => x ^ 4 by measurability );
            convert this.integrable_iff.mpr hX_fourth using 1 ; ext ; ring;
            norm_cast;
          · exact MeasureTheory.AEStronglyMeasurable.pow ( hX_meas i |> Measurable.aestronglyMeasurable ) _;
        · have := hX_ident ( i - j );
          have := this.comp ( measurable_id'.pow_const 2 );
          rw [ memLp_two_iff_integrable_sq ];
          · have := this.comp ( measurable_id'.pow_const 2 );
            convert this.integrable_iff.mpr _ using 1;
            convert hX_fourth using 1 ; ext ; norm_num ; ring;
          · exact MeasureTheory.AEStronglyMeasurable.pow ( hX_meas _ |> Measurable.aestronglyMeasurable ) _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( hX_meas i |> Measurable.aestronglyMeasurable ) ( hX_meas ( i - j ) |> Measurable.aestronglyMeasurable );
      · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun ω => 4 * ( ∑ j ∈ Finset.Icc 1 ( m n ), sampleAutocovariance X ( n + 1 ) j ω ^ 2 ) * ( m n : ℝ );
    · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( MeasureTheory.integrable_finset_sum _ fun j hj => h_integrable j ) _ ) _;
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.pow_const _ _;
      refine' Measurable.mul _ _;
      · exact measurable_const;
      · refine' Finset.measurable_sum _ fun j hj => _;
        refine' Measurable.mul _ _;
        · exact measurable_const;
        · exact Measurable.mul ( measurable_const ) ( Finset.measurable_sum _ fun _ _ => Measurable.mul ( hX_meas _ ) ( hX_meas _ ) );
    · -- Apply the Cauchy-Schwarz inequality to the sum.
      have h_cauchy_schwarz : ∀ ω, (∑ j ∈ Finset.Icc 1 (m n), bartlettWeight j (m n) * sampleAutocovariance X (n + 1) j ω) ^ 2 ≤ (∑ j ∈ Finset.Icc 1 (m n), sampleAutocovariance X (n + 1) j ω ^ 2) * (∑ j ∈ Finset.Icc 1 (m n), bartlettWeight j (m n) ^ 2) := by
        intro ω;
        have h_cauchy_schwarz : ∀ (u v : ℕ → ℝ), (∑ j ∈ Finset.Icc 1 (m n), u j * v j) ^ 2 ≤ (∑ j ∈ Finset.Icc 1 (m n), u j ^ 2) * (∑ j ∈ Finset.Icc 1 (m n), v j ^ 2) := by
          exact fun u v => sum_mul_sq_le_sq_mul_sq (Icc 1 (m n)) u v;
        simpa only [ mul_comm ] using h_cauchy_schwarz ( fun j => sampleAutocovariance X ( n + 1 ) j ω ) ( fun j => bartlettWeight j ( m n ) );
      -- Since $\sum_{j=1}^{m(n)} \text{bartlettWeight}(j, m(n))^2 \leq m(n)$, we can bound the expression.
      have h_sum_bartlettWeight_sq : ∑ j ∈ Finset.Icc 1 (m n), bartlettWeight j (m n) ^ 2 ≤ m n := by
        refine' le_trans ( Finset.sum_le_sum fun i hi => pow_le_one₀ ( bartlettWeight_nonneg i ( m n ) ) ( bartlettWeight_le_one i ( m n ) ) ) _ ; norm_num;
      simp_all +decide [ hacRemainder ];
      filter_upwards [ ] with ω using by rw [ mul_pow, sq_abs ] ; nlinarith only [ h_cauchy_schwarz ω, h_sum_bartlettWeight_sq, show 0 ≤ ∑ j ∈ Finset.Icc 1 ( m n ), sampleAutocovariance X ( n + 1 ) j ω ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ;
  · exact fun n => div_nonneg ( mul_nonneg ( mul_nonneg zero_le_four ( sq_nonneg _ ) ) ( MeasureTheory.integral_nonneg fun _ => by positivity ) ) ( Nat.cast_nonneg _ );
  · have := bandwidth_rate_sq_tendsto m hm_rate;
    convert this.const_mul ( 4 * ∫ ω, X 0 ω ^ 4 ∂μ ) using 2 <;> push_cast <;> ring

/-! ### Main consistency theorem -/

/-
**Newey-West HAC estimator consistency (iid case).**

For an iid sequence `{X_t}` with `E[X_t] = 0`, `E[X_t²] = σ²`, and finite
fourth moment `E[X_t⁴] < ∞`, the Bartlett-kernel HAC estimator

  `Σ̂_T = γ̂(0) + 2 ∑_{j=1}^{m(T)} (1 - j/(m(T)+1)) γ̂(j)`

satisfies `Σ̂_T →_p σ²` whenever the bandwidth `m(T) → ∞` and
`m(T) / T^{1/4} → 0`.

This is the iid special case of Newey & West (1987, Econometrica 55:703–708).
In the iid setting all population autocovariances at lag ≥ 1 vanish, so the
estimator is `γ̂(0)` plus a vanishing remainder. The bandwidth condition
`m(T) / T^{1/4} → 0` is inherited from the general mixing framework and is
automatically satisfied in the iid case with any `m(T) = o(T^{1/4})`.

Reference: Newey, W.K. and West, K.D. (1987).
-/
theorem hac_consistent
    (X : ℕ → Ω → ℝ) (σ_sq : ℝ) (m : ℕ → ℕ)
    (hσ_sq_nonneg : 0 ≤ σ_sq)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_indep : iIndepFun (m := fun (_ : ℕ) => inferInstance) X μ)
    (hX_ident : ∀ t, IdentDistrib (X t) (X 0) μ μ)
    (hX_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hX_var : ∫ ω, X 0 ω ^ 2 ∂μ = σ_sq)
    (hX_int_sq : Integrable (fun ω => X 0 ω ^ 2) μ)
    (hX_fourth : Integrable (fun ω => X 0 ω ^ 4) μ)
    (hm_tendsto : Tendsto (fun T => (m T : ℝ)) atTop atTop)
    (hm_rate : Tendsto (fun T => (m T : ℝ) / (T : ℝ) ^ (1/4 : ℝ)) atTop (nhds 0)) :
    TendstoInMeasure μ
      (fun T ω => hacEstimator X (T + 1) (m T) ω) atTop (fun _ => σ_sq) := by
  intro ε hε;
  -- Apply the triangle inequality to split the measure into two parts.
  have h_triangle : ∀ i, μ {x | ε ≤ edist (hacEstimator X (i + 1) (m i) x) σ_sq} ≤ μ {x | ε / 2 ≤ edist (sampleAutocovariance X (i + 1) 0 x) σ_sq} + μ {x | ε / 2 ≤ edist (hacRemainder X (i + 1) (m i) x) 0} := by
    intro i
    have h_triangle : ∀ x, ε ≤ edist (hacEstimator X (i + 1) (m i) x) σ_sq → ε / 2 ≤ edist (sampleAutocovariance X (i + 1) 0 x) σ_sq ∨ ε / 2 ≤ edist (hacRemainder X (i + 1) (m i) x) 0 := by
      intro x hx
      have h_triangle : edist (hacEstimator X (i + 1) (m i) x) σ_sq ≤ edist (sampleAutocovariance X (i + 1) 0 x) σ_sq + edist (hacRemainder X (i + 1) (m i) x) 0 := by
        rw [ hacEstimator_eq_gamma_zero_add_remainder ];
        simp +decide [ edist_dist, dist_eq_norm ];
        rw [ ← ENNReal.ofReal_add ( abs_nonneg _ ) ( abs_nonneg _ ) ] ; exact ENNReal.ofReal_le_ofReal ( by cases abs_cases ( sampleAutocovariance X ( i + 1 ) 0 x + hacRemainder X ( i + 1 ) ( m i ) x - σ_sq ) <;> cases abs_cases ( sampleAutocovariance X ( i + 1 ) 0 x - σ_sq ) <;> cases abs_cases ( hacRemainder X ( i + 1 ) ( m i ) x ) <;> linarith ) ;
      contrapose! hx;
      exact lt_of_le_of_lt h_triangle ( ENNReal.add_lt_add hx.1 hx.2 |> lt_of_lt_of_le <| by rw [ ENNReal.add_halves ] );
    exact le_trans ( MeasureTheory.measure_mono ( show { x | ε ≤ edist ( hacEstimator X ( i + 1 ) ( m i ) x ) σ_sq } ⊆ { x | ε / 2 ≤ edist ( sampleAutocovariance X ( i + 1 ) 0 x ) σ_sq } ∪ { x | ε / 2 ≤ edist ( hacRemainder X ( i + 1 ) ( m i ) x ) 0 } from fun x hx => h_triangle x hx ) ) ( MeasureTheory.measure_union_le _ _ );
  have h_gamma_zero : Tendsto (fun i => μ {x | ε / 2 ≤ edist (sampleAutocovariance X (i + 1) 0 x) σ_sq}) atTop (nhds 0) := by
    have := gammaHat_zero_tendsto X σ_sq hσ_sq_nonneg hX_meas hX_indep hX_ident hX_mean hX_var hX_int_sq;
    convert this ( ε / 2 ) ( ENNReal.half_pos hε.ne' ) |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 1;
  have h_remainder : Tendsto (fun i => μ {x | ε / 2 ≤ edist (hacRemainder X (i + 1) (m i) x) 0}) atTop (nhds 0) := by
    convert bartlett_remainder_tendsto X m hX_meas hX_indep hX_ident hX_mean hX_int_sq hX_fourth hm_tendsto hm_rate |> fun h => h ( ε / 2 ) ( ENNReal.half_pos hε.ne' ) using 1;
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ( by simpa using h_gamma_zero.add h_remainder ) ( fun i => zero_le _ ) ( fun i => h_triangle i )

end Pythia.TimeSeries.NeweyWest