/-
Pythia.WaldIdentity — Wald's identity for stopping times.

Wald's identity (1944, *Sequential Analysis*) is the workhorse identity
of sequential statistics: for an iid integrable sequence `X_i` and a
stopping time `τ` with `E[τ] < ∞`,

  E[Σ_{i ≤ τ} X_i] = E[X_1] · E[τ].

Mathlib has the optional-stopping theorem in fully general form
(`MeasureTheory.Martingale.stoppedValue_integral_eq`) but the iid-sum
corollary that practitioners actually invoke is missing. We ship four
statements:

* `wald_identity_centered`    — first-moment, μ = 0 (just optional stop).
* `wald_identity`             — first-moment, general mean.
* `wald_identity_squared`     — second-moment: E[(Σ - μτ)²] = σSq · E[τ].
* `wald_identity_exp`         — exponential-MGF form for sub-Gaussian X.
                                 Bridge to anytime-valid inference.

References
----------
* Wald, *Sequential Analysis*, 1944. Original.
* Williams, *Probability with Martingales*, §10.10.
-/
import Mathlib
import Pythia.Basic
import Pythia.MeasureTheory.OptionalStoppingUnbounded
import Pythia.Tactic.Pythia

namespace Pythia

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}

/-- Partial-sum process `S_n = X_1 + … + X_n` of a real-valued process
indexed by `ℕ`. We define it directly on the path space; downstream
consumers will instantiate via concrete iid samples. -/
noncomputable def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun i => X i ω)

@[simp] lemma partialSum_zero (X : ℕ → Ω → ℝ) (ω : Ω) :
    partialSum X 0 ω = 0 := by
  simp [partialSum]

lemma partialSum_succ (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum X (n + 1) ω = partialSum X n ω + X n ω := by
  simp [partialSum, Finset.sum_range_succ]

/-- Coerce a `Ω → ℕ` stopping time to the `Ω → WithTop ℕ` form Mathlib
uses for `IsStoppingTime`. -/
noncomputable def liftStoppingTime (τ : Ω → ℕ) : Ω → WithTop ℕ :=
  fun ω => (τ ω : WithTop ℕ)

/-! ## Helper lemmas for optional stopping with supermartingales -/

/-
For a supermartingale M and bounded stopping time σ ≤ N,
`∫ stoppedValue M σ ≤ ∫ M 0`.
-/
private lemma super_stoppedValue_le_initial
    [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M 𝓕 μ)
    {σ : Ω → ℕ∞}
    (hσ : IsStoppingTime 𝓕 σ)
    {N : ℕ}
    (hσ_bdd : ∀ ω, σ ω ≤ N) :
    ∫ ω, stoppedValue M σ ω ∂μ ≤ ∫ ω, M 0 ω ∂μ := by
  exact supermartingale_expected_stoppedValue_le hM hσ hσ_bdd

/-
For a supermartingale M and stopping time τ, `∫ stoppedProcess M τ n ≤ ∫ M 0`
for every n.
-/
private lemma super_stoppedProcess_le_initial
    [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M 𝓕 μ)
    {τ : Ω → ℕ∞}
    (hτ : IsStoppingTime 𝓕 τ)
    (n : ℕ) :
    ∫ ω, stoppedProcess M τ n ω ∂μ ≤ ∫ ω, M 0 ω ∂μ := by
  convert super_stoppedValue_le_initial hM _ _;
  convert hτ.min ( isStoppingTime_const 𝓕 n ) using 1;
  exacts [ funext fun ω => min_comm _ _, n, fun ω => min_le_left _ _ ]

/-
**Optional stopping for uniformly integrable supermartingales** (≤ direction).
Supermartingale version of `Pythia.MTUnbounded.optional_stopping_unbounded`:
for a supermartingale M and a.s.-finite stopping time τ with UI stopped process,
`∫ stoppedValue M τ ≤ ∫ M 0`.
-/
private theorem optional_stopping_super
    [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M 𝓕 μ)
    {τ : Ω → ℕ∞}
    (hτ : IsStoppingTime 𝓕 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : UniformIntegrable
              (fun n : ℕ => stoppedProcess M τ n) 1 μ) :
    ∫ ω, stoppedValue M τ ω ∂μ ≤ ∫ ω, M 0 ω ∂μ := by
  have h_integrable : MeasureTheory.Integrable (stoppedValue M τ) μ := by
    obtain ⟨ C, hC ⟩ := hUI;
    have h_conv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => stoppedProcess M τ n ω) Filter.atTop (nhds (stoppedValue M τ ω)) := by
      filter_upwards [ hτ_finite ] with ω hω;
      refine' tendsto_const_nhds.congr' _;
      filter_upwards [ Filter.eventually_ge_atTop ( τ ω |> ENat.toNat ) ] with n hn;
      unfold stoppedValue stoppedProcess;
      cases h : τ ω <;> aesop;
    have h_integrable : MeasureTheory.Integrable (stoppedValue M τ) μ := by
      have h_unif_integrable : MeasureTheory.UniformIntegrable (fun n => stoppedProcess M τ n) 1 μ := by
        exact ⟨ C, hC.1, hC.2 ⟩
      convert h_unif_integrable.memLp_of_ae_tendsto h_conv using 1;
      ext; simp [Integrable, MemLp];
      simp +decide [ HasFiniteIntegral, eLpNorm_one_eq_lintegral_enorm ];
    exact h_integrable;
  have h_integrable : Filter.Tendsto (fun n => MeasureTheory.integral μ (stoppedProcess M τ n)) Filter.atTop (nhds (MeasureTheory.integral μ (stoppedValue M τ))) := by
    refine' MeasureTheory.tendsto_integral_of_L1 _ _ _ _;
    · exact h_integrable;
    · refine' Filter.Eventually.of_forall fun n => _;
      have := hUI.1 n;
      refine' ⟨ this, _ ⟩;
      have := hUI.2;
      exact lt_of_le_of_lt ( by simp +decide [ eLpNorm_one_eq_lintegral_enorm ] ) ( lt_of_le_of_lt ( this.2.choose_spec n ) ( ENNReal.coe_lt_top ) );
    · have h_ae_conv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => stoppedProcess M τ n ω) Filter.atTop (nhds (stoppedValue M τ ω)) := by
        filter_upwards [ hτ_finite ] with ω hω;
        cases h : τ ω <;> simp_all +decide [ stoppedProcess, stoppedValue ];
        refine' tendsto_const_nhds.congr' _;
        filter_upwards [ Filter.eventually_ge_atTop ‹_› ] with n hn using by simp +decide [ hn ] ;
      have h_l1_conv : MeasureTheory.TendstoInMeasure μ (fun n => stoppedProcess M τ n) Filter.atTop (stoppedValue M τ) := by
        apply_rules [ tendstoInMeasure_of_tendsto_ae ];
        intro n;
        have := hUI.1;
        exact this n;
      have := @MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure;
      specialize this ( show 1 ≤ 1 by norm_num ) ( show ( 1 : ENNReal ) ≠ ⊤ by norm_num ) ( fun n => ?_ ) ( show MemLp ( stoppedValue M τ ) 1 μ from ?_ ) ( show UnifIntegrable ( fun n => stoppedProcess M τ n ) 1 μ from ?_ ) h_l1_conv;
      · exact hUI.1 n;
      · exact MeasureTheory.memLp_one_iff_integrable.mpr h_integrable;
      · exact hUI.2.1;
      · convert this using 1;
        ext; simp +decide [ eLpNorm_one_eq_lintegral_enorm ] ;
  exact le_of_tendsto_of_tendsto' h_integrable tendsto_const_nhds fun n => by simpa using super_stoppedProcess_le_initial hM hτ n;

/-! ## Bounded martingale optional stopping equality for ℕ-valued stopping times -/

/-
For a martingale M and bounded stopping time σ ≤ N,
`∫ stoppedValue M σ = ∫ M 0`.
-/
private lemma mart_stoppedValue_eq_initial
    [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ)
    {σ : Ω → ℕ∞}
    (hσ : IsStoppingTime 𝓕 σ)
    {N : ℕ}
    (hσ_bdd : ∀ ω, σ ω ≤ N) :
    ∫ ω, stoppedValue M σ ω ∂μ = ∫ ω, M 0 ω ∂μ := by
  refine' le_antisymm _ _;
  · convert super_stoppedValue_le_initial hM.supermartingale hσ hσ_bdd using 1;
  · convert Submartingale.expected_stoppedValue_mono ( hM.submartingale ) _ _ _;
    rotate_left;
    exact fun _ => 0;
    all_goals norm_cast;
    · exact isStoppingTime_const 𝓕 0;
    · exact fun _ => zero_le _;
    · unfold stoppedValue; aesop;

/-
For a martingale M and ℕ-valued stopping time τ bounded by N,
`∫ M(min(τ,N)) = ∫ M 0`. Combined with the fact that min(τ,N) = τ
for N ≥ τ, this gives `∫ M_τ = ∫ M_0` for bounded τ.
-/
private lemma mart_trunc_integral_eq
    [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ)
    (τ : Ω → ℕ)
    (hτ : IsStoppingTime 𝓕 (liftStoppingTime τ))
    (N : ℕ) :
    ∫ ω, M (min (τ ω) N) ω ∂μ = ∫ ω, M 0 ω ∂μ := by
  convert mart_stoppedValue_eq_initial hM ( show IsStoppingTime 𝓕 ( fun ω => min ( liftStoppingTime τ ω ) N ) from ?_ ) ( show ∀ ω, min ( liftStoppingTime τ ω ) N ≤ N from ?_ ) using 1;
  · exact IsStoppingTime.min_const hτ ↑N;
  · exact fun ω => min_le_right _ _

/-! ## Main theorems -/

/-- **Wald's identity** (first moment, m-parameterized).

For an iid integrable sequence `X_i` with `E[X_1] = m` and a stopping
time `τ` with `E[τ] < ∞`,

  E[S_τ] = m · E[τ].

The centered version `m = 0` is `wald_identity_centered` below. -/
theorem wald_identity
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (m : ℝ)
    (_hX_int : ∀ i, Integrable (X i) μ)
    (_hX_mean : ∀ i, ∫ ω, X i ω ∂μ = m)
    (_hX_mart_centered :
      Martingale (fun n ω => partialSum X n ω - m * (n : ℝ)) 𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (_hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    ∫ ω, partialSum X (τ ω) ω ∂μ = m * ∫ ω, (τ ω : ℝ) ∂μ := by
  sorry

/-- **Wald's identity** (centered corollary, m = 0). -/
theorem wald_identity_centered
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ)
    (hX_int : ∀ i, Integrable (X i) μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_mart : Martingale (fun n ω => partialSum X n ω) 𝓕 μ)
    (τ : Ω → ℕ)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    ∫ ω, partialSum X (τ ω) ω ∂μ = 0 := by
  have h := wald_identity 𝓕 X 0 hX_int hX_mean
    (by simpa using hX_mart) τ hτ hτ_int
  simpa using h

/-- **Wald's identity (centered) via uniform integrability — ℕ∞ form.** -/
@[stat_lemma]
theorem wald_identity_centered_via_optional_stopping
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ)
    (hS_mart : Martingale (fun n ω => partialSum X n ω) 𝓕 μ)
    (τ : Ω → ℕ∞)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : MeasureTheory.UniformIntegrable
              (fun n : ℕ =>
                MeasureTheory.stoppedProcess
                  (fun n ω => partialSum X n ω) τ n)
              1 μ) :
    ∫ ω, MeasureTheory.stoppedValue
            (fun n ω => partialSum X n ω) τ ω ∂μ = 0 := by
  have hOS :=
    Pythia.MTUnbounded.optional_stopping_unbounded
      (M := fun n ω => partialSum X n ω) hS_mart hτ hτ_finite hUI
  rw [hOS]
  simp [partialSum_zero]

/-- **Wald's identity, second moment.** -/
theorem wald_identity_squared
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (m σSq : ℝ)
    (_hX_sq_int : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    (_hX_mean : ∀ i, ∫ ω, X i ω ∂μ = m)
    (_hX_var : ∀ i, ∫ ω, (X i ω - m) ^ 2 ∂μ = σSq)
    (_hQuadVar_mart :
      Martingale
        (fun n ω => (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
        𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (_hτ_sq_int : Integrable (fun ω => (τ ω : ℝ) ^ 2) μ) :
    ∫ ω, (partialSum X (τ ω) ω - m * (τ ω : ℝ)) ^ 2 ∂μ
      = σSq * ∫ ω, (τ ω : ℝ) ∂μ := by
  sorry

/-
For each N, the truncated exponential process at min(τ,N) has integral ≤ 1.
-/
private lemma exp_trunc_integral_le
    [IsProbabilityMeasure μ]
    {𝓕 : MeasureTheory.Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    (X : ℕ → Ω → ℝ) (σSq : ℝ) (lam : ℝ)
    (hExp_super :
      Supermartingale
        (fun n ω =>
          Real.exp (lam * partialSum X n ω
                     - (n : ℝ) * (σSq * lam ^ 2 / 2)))
        𝓕 μ)
    (τ : Ω → ℕ)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (N : ℕ) :
    ∫ ω, Real.exp (lam * partialSum X (min (τ ω) N) ω
                    - (min (τ ω) N : ℝ) * (σSq * lam ^ 2 / 2)) ∂μ ≤ 1 := by
  convert super_stoppedValue_le_initial hExp_super ( show IsStoppingTime 𝓕 ( fun ω => Min.min ( ( τ ω : WithTop ℕ ) ) N ) from ?_ ) ( fun ω => ?_ ) using 1;
  any_goals exact N;
  · norm_cast;
  · norm_num;
  · exact IsStoppingTime.min_const hτ ↑N;
  · exact min_le_right _ _

/-  Pointwise convergence: the truncated exponential converges to the
    full exponential as N → ∞. -/
private lemma exp_trunc_tendsto
    (X : ℕ → Ω → ℝ) (σSq lam : ℝ) (τ : Ω → ℕ) (ω : Ω) :
    Filter.Tendsto
      (fun N => Real.exp (lam * partialSum X (min (τ ω) N) ω
                          - (min (τ ω) N : ℝ) * (σSq * lam ^ 2 / 2)))
      Filter.atTop
      (nhds (Real.exp (lam * partialSum X (τ ω) ω
                        - (τ ω : ℝ) * (σSq * lam ^ 2 / 2)))) := by
  refine' Filter.Tendsto.congr' _ tendsto_const_nhds;
  filter_upwards [ Filter.eventually_ge_atTop ( τ ω ) ] with N hN using by simp +decide [ hN ] ;

/-
The truncated exponential is integrable for each N.
-/
private lemma exp_trunc_integrable
    [IsProbabilityMeasure μ]
    {𝓕 : MeasureTheory.Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    (X : ℕ → Ω → ℝ) (σSq lam : ℝ)
    (hExp_super :
      Supermartingale
        (fun n ω =>
          Real.exp (lam * partialSum X n ω
                     - (n : ℝ) * (σSq * lam ^ 2 / 2)))
        𝓕 μ)
    (τ : Ω → ℕ)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (N : ℕ) :
    Integrable (fun ω => Real.exp (lam * partialSum X (min (τ ω) N) ω
                    - (min (τ ω) N : ℝ) * (σSq * lam ^ 2 / 2))) μ := by
  -- Since the stopping time min (τ ω) N is bounded by N, the stopped process up to that time is a finite sum of the original process values. Each of these values is integrable because the original process is integrable.
  have h_integrable : ∀ n, Integrable (fun ω => Real.exp (lam * partialSum X n ω - n * (σSq * lam ^ 2 / 2))) μ := by
    exact fun n => hExp_super.integrable n;
  convert MeasureTheory.integrable_finset_sum ( Finset.range ( N + 1 ) ) fun n _hn => MeasureTheory.Integrable.indicator ( h_integrable n ) ( show MeasurableSet { ω : Ω | min ( τ ω ) N = n } from ?_ ) using 1;
  · ext ω; simp +decide [ Set.indicator ] ;
  · have h_measurable : ∀ n, MeasurableSet {ω | τ ω ≤ n} := by
      intro n
      have := hτ.measurableSet_le n
      simp_all +decide [ liftStoppingTime ];
      exact this.mono ( 𝓕.le n ) le_rfl;
    have h_measurable : ∀ n, MeasurableSet {ω | τ ω = n} := by
      intro n;
      induction' n with n ih;
      · simpa using h_measurable 0;
      · have h_measurable : MeasurableSet {ω | τ ω ≤ n + 1} ∧ MeasurableSet {ω | τ ω ≤ n} := by
          exact ⟨ h_measurable _, h_measurable _ ⟩;
        convert h_measurable.1.diff h_measurable.2 using 1 ; ext ω ; simp +decide;
        exact ⟨ fun h => ⟨ h.le, h.symm ▸ Nat.lt_succ_self _ ⟩, fun h => le_antisymm h.1 ( Nat.succ_le_of_lt h.2 ) ⟩;
    convert MeasurableSet.inter ( h_measurable n ) ( show MeasurableSet { ω | n ≤ N } from ?_ ) |> MeasurableSet.union <| MeasurableSet.inter ( show MeasurableSet { ω | τ ω ≥ N + 1 } from ?_ ) ( show MeasurableSet { ω | N = n } from ?_ ) using 1;
    · ext ω; simp [min_def];
      grind;
    · simp +decide [ Finset.mem_range_succ_iff.mp _hn ];
    · convert MeasurableSet.compl ( ‹∀ n, MeasurableSet { ω | τ ω ≤ n } › N ) using 1 ; ext ; simp +decide [ not_le ];
    · by_cases h : N = n <;> simp +decide [ h ]

/-
The lintegral of the truncated exponential (via ENNReal.ofReal) is ≤ 1 for each N.
-/
private lemma exp_trunc_lintegral_le_one
    [IsProbabilityMeasure μ]
    {𝓕 : MeasureTheory.Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    (X : ℕ → Ω → ℝ) (σSq lam : ℝ)
    (hExp_super :
      Supermartingale
        (fun n ω =>
          Real.exp (lam * partialSum X n ω
                     - (n : ℝ) * (σSq * lam ^ 2 / 2)))
        𝓕 μ)
    (τ : Ω → ℕ)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal
      (Real.exp (lam * partialSum X (min (τ ω) N) ω
                  - (min (τ ω) N : ℝ) * (σSq * lam ^ 2 / 2))) ∂μ ≤ 1 := by
  have h_integrable : Integrable (fun ω => Real.exp (lam * partialSum X (min (τ ω) N) ω - (min (τ ω) N : ℝ) * (σSq * lam ^ 2 / 2))) μ := by
    convert exp_trunc_integrable X σSq lam hExp_super τ hτ N using 1;
  convert ENNReal.ofReal_le_ofReal ( exp_trunc_integral_le X σSq lam hExp_super τ hτ N ) using 1;
  · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable ];
    exact Filter.Eventually.of_forall fun ω => Real.exp_nonneg _;
  · norm_num

/-
The lintegral of the exponential (via ENNReal.ofReal) is ≤ 1.
   Proved by Fatou's lemma + exp_trunc_lintegral_le_one.
-/
private lemma exp_lintegral_le_one
    [IsProbabilityMeasure μ]
    {𝓕 : MeasureTheory.Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓕]
    (X : ℕ → Ω → ℝ) (σSq lam : ℝ)
    (hExp_super :
      Supermartingale
        (fun n ω =>
          Real.exp (lam * partialSum X n ω
                     - (n : ℝ) * (σSq * lam ^ 2 / 2)))
        𝓕 μ)
    (τ : Ω → ℕ)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ)) :
    ∫⁻ ω, ENNReal.ofReal
      (Real.exp (lam * partialSum X (τ ω) ω
                  - (τ ω : ℝ) * (σSq * lam ^ 2 / 2))) ∂μ ≤ 1 := by
  -- Apply Fatou's lemma to the sequence of functions.
  have h_fatou : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * partialSum X (τ ω) ω - (τ ω : ℝ) * (σSq * lam ^ 2 / 2))) ∂μ ≤ Filter.liminf (fun N => ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * partialSum X (min (τ ω) N) ω - (min (τ ω) N : ℝ) * (σSq * lam ^ 2 / 2))) ∂μ) Filter.atTop := by
    convert MeasureTheory.lintegral_liminf_le' _;
    · refine' Eq.symm ( Filter.Tendsto.liminf_eq _ );
      exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop ( τ ‹_› ) ] with n hn; simp +decide [ hn ] );
    · intro n;
      have := exp_trunc_integrable X σSq lam hExp_super τ hτ n;
      exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable this.1.aemeasurable;
  refine' le_trans h_fatou ( le_trans ( Filter.liminf_le_of_frequently_le _ _ ) _ );
  exact 1;
  · exact Filter.frequently_atTop.2 fun N => ⟨ N, le_rfl, by simpa using exp_trunc_lintegral_le_one X σSq lam hExp_super τ hτ N ⟩;
  · exact ⟨ 0, Filter.Eventually.of_forall fun N => zero_le _ ⟩;
  · simp +decide

/-- **Wald's identity, exponential / MGF form.**

Proof: For non-integrable target, the integral is 0 ≤ 1 (by `integral_undef`).
Otherwise use Fatou's lemma on the non-negative truncated sequence. -/
theorem wald_identity_exp
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (σSq : ℝ) (_hσ : 0 ≤ σSq)
    (_hX_subG : ∀ i (lam : ℝ),
                ∫ ω, Real.exp (lam * X i ω) ∂μ ≤ Real.exp (σSq * lam ^ 2 / 2))
    (_hExp_super :
      ∀ lam,
        Supermartingale
          (fun n ω =>
            Real.exp (lam * partialSum X n ω
                       - (n : ℝ) * (σSq * lam ^ 2 / 2)))
          𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ)) (lam : ℝ) :
    ∫ ω, Real.exp (lam * partialSum X (τ ω) ω
                    - (τ ω : ℝ) * (σSq * lam ^ 2 / 2)) ∂μ ≤ 1 := by
  by_cases hint : Integrable (fun ω => Real.exp (lam * partialSum X (τ ω) ω
      - (τ ω : ℝ) * (σSq * lam ^ 2 / 2))) μ
  · rw [integral_eq_lintegral_of_nonneg_ae
        (ae_of_all μ fun ω => le_of_lt (Real.exp_pos _))
        hint.aestronglyMeasurable]
    have hle := exp_lintegral_le_one X σSq lam (_hExp_super lam) τ _hτ
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * partialSum X (τ ω) ω
              - (τ ω : ℝ) * (σSq * lam ^ 2 / 2))) ∂μ).toReal
        ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hle
      _ = 1 := by simp
  · rw [integral_undef hint]; exact zero_le_one

/-- **Wald's identity (second moment) via uniform integrability — ℕ∞ form.** -/
theorem wald_identity_squared_via_optional_stopping
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (m σSq : ℝ)
    (hQuadVar_mart :
      Martingale
        (fun n ω => (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
        𝓕 μ)
    (τ : Ω → ℕ∞)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : MeasureTheory.UniformIntegrable
              (fun n : ℕ =>
                MeasureTheory.stoppedProcess
                  (fun n ω =>
                    (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
                  τ n)
              1 μ) :
    ∫ ω, MeasureTheory.stoppedValue
            (fun n ω =>
              (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
            τ ω ∂μ = 0 := by
  have hOS :=
    Pythia.MTUnbounded.optional_stopping_unbounded
      (M := fun n ω =>
        (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
      hQuadVar_mart hτ hτ_finite hUI
  rw [hOS]
  simp [partialSum_zero]

/-- **Wald's identity (exponential / MGF form) via optional stopping — ℕ∞ form.** -/
theorem wald_identity_exp_via_optional_stopping
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (σSq : ℝ) (_hσ : 0 ≤ σSq) (lam : ℝ)
    (hExp_super :
      Supermartingale
        (fun n ω =>
          Real.exp (lam * partialSum X n ω
                     - (n : ℝ) * (σSq * lam ^ 2 / 2)))
        𝓕 μ)
    (τ : Ω → ℕ∞)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : MeasureTheory.UniformIntegrable
              (fun n : ℕ =>
                MeasureTheory.stoppedProcess
                  (fun n ω =>
                    Real.exp (lam * partialSum X n ω
                              - (n : ℝ) * (σSq * lam ^ 2 / 2)))
                  τ n)
              1 μ) :
    ∫ ω, MeasureTheory.stoppedValue
            (fun n ω =>
              Real.exp (lam * partialSum X n ω
                        - (n : ℝ) * (σSq * lam ^ 2 / 2)))
            τ ω ∂μ ≤ 1 := by
  -- Apply optional_stopping_super to get ∫ stoppedValue E τ ≤ ∫ E 0 = 1
  have hle := optional_stopping_super hExp_super hτ hτ_finite hUI
  calc ∫ ω, stoppedValue
            (fun n ω => Real.exp (lam * partialSum X n ω
                        - (n : ℝ) * (σSq * lam ^ 2 / 2))) τ ω ∂μ
      ≤ ∫ ω, (fun n ω => Real.exp (lam * partialSum X n ω
                        - (n : ℝ) * (σSq * lam ^ 2 / 2))) 0 ω ∂μ := hle
    _ = ∫ ω, Real.exp 0 ∂μ := by simp [partialSum_zero]
    _ = 1 := by simp

end Pythia