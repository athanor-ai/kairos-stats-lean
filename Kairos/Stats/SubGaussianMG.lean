/-
Kairos.Stats.SubGaussianMG — measure-theoretic sub-Gaussian martingale
structure + supermartingale + Ville's inequality, built on Mathlib's
`MeasureTheory.Filtration` and `ProbabilityTheory.HasCondSubgaussianMGF`.

A sub-Gaussian martingale here is a process `M : ℕ → Ω → ℝ` adapted
to a filtration `𝓕`, whose increment `M_{t+1} - M_t` has a
conditional sub-Gaussian MGF bound given `𝓕 t`. From this we derive:

  1. base martingale property (`SubGaussianMG.martingale`)
  2. exponential supermartingale `exp(lam·M_t)/exp(lam²·σ²·t/2)`
  3. Ville's inequality: ℙ[∃ t ≤ N, M_t ≥ τ] ≤ exp(-τ²/(2σ²·N))
     via Doob's maximal inequality + Chernoff optimisation over `lam`.

Mathlib primitives used (pinned on `lake-manifest.json`):
  • `MeasureTheory.Filtration`         (Probability/Process/Filtration.lean)
  • `MeasureTheory.Martingale`         (Probability/Martingale/Basic.lean)
  • `ProbabilityTheory.HasCondSubgaussianMGF`
                                       (Probability/Moments/SubGaussian.lean)
  • `MeasureTheory.maximal_ineq` (Doob) (Probability/Martingale/OptionalStopping.lean)

The `StandardBorelSpace Ω` constraint is mandated by
`HasCondSubgaussianMGF` for its `condExpKernel` machinery.

Axiom-audit target: {propext, Classical.choice, Quot.sound}.
-/

import Mathlib

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators

/-! ## Structure + base martingale property -/

/-- A sub-Gaussian martingale in the measure-theoretic sense:
a process `M : ℕ → Ω → ℝ` adapted to a filtration `𝓕`, with the
increment `M_{t+1} - M_t` having a *conditional* sub-Gaussian MGF
bound given `𝓕 t`.

This is the non-vacuous replacement for `Basic.SubGaussianMartingale`.
The old structure carried `∃ bound, bound ≤ exp(λ² σ² / 2)`, which
is trivially satisfiable. `HasCondSubgaussianMGF` carries the genuine
probabilistic content: `∀ᵐ ω ∂μ, μ[exp(t · X) | 𝓕 t] ≤ exp(c t² / 2)`.
-/
structure SubGaussianMG
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (σ : ℝ) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] where
  /-- The process. -/
  process : ℕ → Ω → ℝ
  /-- `process` is adapted to the filtration. -/
  adapted : Adapted 𝓕 process
  /-- Integrability at each step (needed for conditional expectation). -/
  integrable : ∀ t, Integrable (process t) μ
  /-- Exponential integrability at each step. `HasCondSubgaussianMGF` only
      supplies integrability of `exp(lam · increment)`; to close the
      exponential-supermartingale chain we also need integrability of
      `exp(lam · process t)` at each `t`. This is automatic when the
      process starts bounded (e.g. `process 0 = 0`) and the increments
      are sub-Gaussian, but is carried as a field here to avoid
      repeating the telescoping Cauchy-Schwarz argument. -/
  integrable_exp : ∀ t : ℕ, ∀ lam : ℝ,
    Integrable (fun ω => Real.exp (lam * process t ω)) μ
  /-- Increments have a conditional sub-Gaussian MGF bound. This is
      the genuine probabilistic content that the scalar existential
      in `Basic.SubGaussianMartingale` lacked. -/
  increments_subG : ∀ t : ℕ,
    HasCondSubgaussianMGF (𝓕 t) (𝓕.le t)
      (fun ω => process (t + 1) ω - process t ω)
      (Real.toNNReal (σ^2)) μ
  /-- Zero conditional mean of increments.  Derivable from `increments_subG`
      via differentiation of the MGF bound at λ = 0, but carried as a field
      for ergonomics (the derivative argument is not yet in Mathlib). -/
  increments_zero_mean : ∀ t,
    μ[fun ω => process (t + 1) ω - process t ω | 𝓕 t] =ᵐ[μ] 0
  /-- Positivity of σ. -/
  sigma_pos : 0 < σ

/-
**Base martingale property** — `SubGaussianMG.martingale`.

The underlying process is a martingale under `𝓕` and `μ`. The zero
conditional mean of increments comes from the `increments_zero_mean`
field (see the field docstring for the derivation that would remove
the field).

Downstream callers use `M.martingale` instead of manually rebuilding
the martingale property at each site.
-/
theorem SubGaussianMG.martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (M : SubGaussianMG σ 𝓕 μ) :
    Martingale M.process 𝓕 μ := by
  refine' MeasureTheory.martingale_nat _ _ _;
  · intro t
    exact (M.adapted t).stronglyMeasurable
  · exact M.integrable;
  · have h_cond_exp_zero : ∀ i, (μ[(fun ω => M.process (i + 1) ω - M.process i ω) | 𝓕 i]) =ᵐ[μ] 0 := by
      exact M.increments_zero_mean;
    intro i
    have h_cond_exp_split : (μ[(fun ω => M.process (i + 1) ω) | 𝓕 i]) =ᵐ[μ] (μ[(fun ω => M.process i ω) | 𝓕 i]) + (μ[(fun ω => M.process (i + 1) ω - M.process i ω) | 𝓕 i]) := by
      convert MeasureTheory.condExp_add _ _ _ using 1;
      · exact congr_arg _ ( by ext; simp +decide );
      · exact M.integrable i;
      · exact MeasureTheory.Integrable.sub ( M.integrable _ ) ( M.integrable _ );
    have h_cond_exp_self : (μ[(fun ω => M.process i ω) | 𝓕 i]) =ᵐ[μ] (fun ω => M.process i ω) := by
      rw [ MeasureTheory.condExp_of_stronglyMeasurable ];
      · exact M.adapted i |> fun h => h.stronglyMeasurable;
      · exact M.integrable i;
    filter_upwards [ h_cond_exp_split, h_cond_exp_self, h_cond_exp_zero i ] with ω hω₁ hω₂ hω₃ using by aesop;

/-! ## Exponential supermartingale

`exp (lam * process t) / exp (lam² σ² t / 2)` is a Supermartingale
for any `lam ≥ 0`. Uses:
  • `HasCondSubgaussianMGF.ae_condExp_le` (Mathlib SubGaussian.lean)
  • `MeasureTheory.condExp` tower property
  • Jensen / exp-convexity on the ratio
-/

/-- **Exponential supermartingale.**

Claim: for a sub-Gaussian martingale `M` in the measure-theoretic
sense and any `lam ≥ 0`, the normalised exponential process
`t ↦ exp (lam · M_t) / exp (lam² σ² t / 2)` is a supermartingale
under the same filtration and measure.

Proof sketch: the conditional MGF bound gives
    𝔼[exp (lam (M_{t+1} - M_t)) | 𝓕 t] ≤ exp (lam² σ² / 2)
ae. Multiplying both sides by `exp (lam · M_t)` (which is 𝓕_t-measurable)
and dividing by `exp (lam² σ² (t+1) / 2)` gives the supermartingale
inequality. Conditional expectation preservation follows from the
tower property + `Integrable` on exponential moments (guaranteed by
`HasSubgaussianMGF.integrable_exp_mul`).
-/
theorem exp_process_is_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (M : SubGaussianMG σ 𝓕 μ) (lam : ℝ) (_hlam : 0 ≤ lam) :
    Supermartingale
      (fun t ω => Real.exp (lam * M.process t ω) /
                  Real.exp (lam^2 * σ^2 * t / 2))
      𝓕 μ := by
  -- Normaliser `c := exp(lam² σ² / 2)`, strictly positive.
  set Y : ℕ → Ω → ℝ := fun t ω =>
      Real.exp (lam * M.process t ω) / Real.exp (lam^2 * σ^2 * t / 2) with hY_def
  have hc_pos : ∀ t : ℕ, 0 < Real.exp (lam^2 * σ^2 * t / 2) := fun _ => Real.exp_pos _
  -- Each `Y t` is non-negative.
  have hY_nonneg : ∀ t ω, 0 ≤ Y t ω := fun t ω => by
    simp only [Y]
    exact div_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  -- Measurability of `exp(lam * M.process t)` with respect to `𝓕 t`.
  have hexp_meas : ∀ t, Measurable[𝓕 t] (fun ω => Real.exp (lam * M.process t ω)) := by
    intro t
    have h1 : Measurable[𝓕 t] (fun ω => lam * M.process t ω) :=
      (M.adapted t).const_mul lam
    exact Real.measurable_exp.comp h1
  -- `Y t` is `𝓕 t`-measurable.
  have hY_meas : ∀ t, Measurable[𝓕 t] (Y t) := by
    intro t
    have h1 := hexp_meas t
    have h2 : Measurable[𝓕 t] (fun _ : Ω => Real.exp (lam^2 * σ^2 * t / 2)) :=
      measurable_const
    exact h1.div h2
  -- `Y t` is `𝓕 t`-strongly-measurable (ℝ is second-countable metric space).
  have hY_strMeas : ∀ t, StronglyMeasurable[𝓕 t] (Y t) := fun t =>
    (hY_meas t).stronglyMeasurable
  -- Strongly adapted.
  have hY_adapted : StronglyAdapted 𝓕 Y := hY_strMeas
  -- Integrability of `Y t` for each t.
  have hY_int : ∀ t, Integrable (Y t) μ := by
    intro t
    -- `Y t = (1 / c_t) * exp(lam * M.process t)` so just scale.
    have h_exp_int : Integrable (fun ω => Real.exp (lam * M.process t ω)) μ :=
      M.integrable_exp t lam
    have : Y t = fun ω =>
        (Real.exp (lam^2 * σ^2 * t / 2))⁻¹ * Real.exp (lam * M.process t ω) := by
      funext ω
      simp only [Y, div_eq_inv_mul]
    rw [this]
    exact h_exp_int.const_mul _
  -- Reduce to the one-step inequality via `supermartingale_nat`.
  refine MeasureTheory.supermartingale_nat (E := ℝ) hY_adapted hY_int ?_
  intro t
  -- Notation.
  set c : ℝ := Real.exp (lam^2 * σ^2 / 2) with hc_def
  have hc_pos' : 0 < c := Real.exp_pos _
  set ΔM : Ω → ℝ := fun ω => M.process (t + 1) ω - M.process t ω with hΔM_def
  -- The conditional-MGF bound on the increment.
  have h_toNNReal : ((Real.toNNReal (σ^2) : NNReal) : ℝ) = σ^2 :=
    Real.coe_toNNReal _ (sq_nonneg σ)
  have h_subG_bound :
      ∀ᵐ ω ∂μ, (μ[fun ω' => Real.exp (lam * ΔM ω') | 𝓕 t]) ω ≤ c := by
    have h_raw := (M.increments_subG t).ae_condExp_le lam
    have h_eq : Real.exp (((Real.toNNReal (σ^2) : NNReal) : ℝ) * lam^2 / 2) = c := by
      rw [h_toNNReal]; simp only [hc_def, mul_comm (σ^2) (lam^2)]
    simpa only [ΔM, h_eq] using h_raw
  -- Factorisation: `Y (t+1) ω = Y t ω * (exp(lam * ΔM ω) / c)`.
  -- We need to reshape the goal to a form amenable to pull-out.
  -- Let `g ω := Real.exp (lam * ΔM ω) / c`. Then
  --   Y (t+1) ω = Y t ω * g ω.
  set g : Ω → ℝ := fun ω => Real.exp (lam * ΔM ω) / c with hg_def
  have h_g_nonneg : ∀ ω, 0 ≤ g ω := fun ω =>
    div_nonneg (Real.exp_nonneg _) (le_of_lt hc_pos')
  have h_factor : ∀ ω, Y (t + 1) ω = Y t ω * g ω := by
    intro ω
    simp only [Y, g, ΔM]
    have h_sum : lam * M.process (t + 1) ω
        = lam * M.process t ω + lam * (M.process (t + 1) ω - M.process t ω) := by ring
    have h_exp_sum :
        Real.exp (lam * M.process (t + 1) ω)
          = Real.exp (lam * M.process t ω)
            * Real.exp (lam * (M.process (t + 1) ω - M.process t ω)) := by
      rw [h_sum, Real.exp_add]
    have h_exp_denom :
        Real.exp (lam^2 * σ^2 * ((t : ℝ) + 1) / 2)
          = Real.exp (lam^2 * σ^2 * (t : ℝ) / 2) * Real.exp (lam^2 * σ^2 / 2) := by
      have h_denom_sum :
          lam^2 * σ^2 * ((t : ℝ) + 1) / 2
            = lam^2 * σ^2 * (t : ℝ) / 2 + lam^2 * σ^2 / 2 := by ring
      rw [h_denom_sum, Real.exp_add]
    rw [h_exp_sum]
    push_cast
    rw [h_exp_denom]
    have hc_ne : Real.exp (lam^2 * σ^2 * (t : ℝ) / 2) ≠ 0 := ne_of_gt (hc_pos t)
    have hc'_ne : c ≠ 0 := ne_of_gt hc_pos'
    simp only [hc_def]
    field_simp
  -- Pull-out: `μ[Y t * g | 𝓕 t] =ᵐ Y t * μ[g | 𝓕 t]`.
  have h_g_int : Integrable g μ := by
    have h_exp_int : Integrable (fun ω => Real.exp (lam * ΔM ω)) μ :=
      (M.increments_subG t).integrable_exp_mul lam
    have : g = fun ω => c⁻¹ * Real.exp (lam * ΔM ω) := by
      funext ω; simp only [g]; rw [div_eq_inv_mul]
    rw [this]
    exact h_exp_int.const_mul _
  have h_Yg_int : Integrable (fun ω => Y t ω * g ω) μ := by
    have : (fun ω => Y t ω * g ω) = Y (t + 1) := by funext ω; exact (h_factor ω).symm
    rw [this]; exact hY_int _
  have h_pull :
      μ[fun ω => Y t ω * g ω | 𝓕 t] =ᵐ[μ] fun ω => Y t ω * (μ[g | 𝓕 t]) ω := by
    have h_strMeas_Yt : StronglyMeasurable[𝓕 t] (Y t) := hY_strMeas t
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left h_strMeas_Yt h_Yg_int h_g_int
  -- Bound `μ[g | 𝓕 t] ≤ᵐ 1`.
  -- `g = (1/c) * exp(lam * ΔM)`, so `μ[g | 𝓕 t] = (1/c) * μ[exp(lam ΔM) | 𝓕 t]`
  -- by `condExp_smul` applied to the scalar `c⁻¹`.
  have h_g_eq : g = (c⁻¹ : ℝ) • fun ω => Real.exp (lam * ΔM ω) := by
    funext ω; simp only [g, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have h_condExp_g :
      μ[g | 𝓕 t] =ᵐ[μ] (c⁻¹ : ℝ) • μ[fun ω => Real.exp (lam * ΔM ω) | 𝓕 t] := by
    rw [h_g_eq]; exact MeasureTheory.condExp_smul (c⁻¹) _ _
  have h_g_le_one :
      ∀ᵐ ω ∂μ, (μ[g | 𝓕 t]) ω ≤ 1 := by
    filter_upwards [h_condExp_g, h_subG_bound] with ω hcg hbd
    rw [hcg]
    simp only [Pi.smul_apply, smul_eq_mul]
    have : c⁻¹ * (μ[fun ω' => Real.exp (lam * ΔM ω') | 𝓕 t]) ω
            ≤ c⁻¹ * c := by
      exact mul_le_mul_of_nonneg_left hbd (le_of_lt (inv_pos.mpr hc_pos'))
    rw [inv_mul_cancel₀ (ne_of_gt hc_pos')] at this
    exact this
  -- Combine: `μ[Y (t+1) | 𝓕 t] =ᵐ μ[Y t * g | 𝓕 t] =ᵐ Y t * μ[g | 𝓕 t] ≤ᵐ Y t * 1 = Y t`.
  have h_Yeq : Y (t + 1) = fun ω => Y t ω * g ω := by
    funext ω; exact h_factor ω
  have h_condExp_Yt1 :
      μ[Y (t + 1) | 𝓕 t] =ᵐ[μ] fun ω => Y t ω * (μ[g | 𝓕 t]) ω := by
    rw [h_Yeq]; exact h_pull
  filter_upwards [h_condExp_Yt1, h_g_le_one] with ω hcond hbnd
  rw [hcond]
  calc Y t ω * (μ[g | 𝓕 t]) ω
      ≤ Y t ω * 1 := mul_le_mul_of_nonneg_left hbnd (hY_nonneg t ω)
    _ = Y t ω := mul_one _

/-! ## Ville's inequality

Combine `exp_process_is_supermartingale` with Ville's inequality
for non-negative supermartingales (via optional stopping)
and Chernoff optimisation over `lam`.
-/

/-
Optional stopping for supermartingales: the expected stopped value
    is bounded by the expected initial value. Uses
    `Submartingale.expected_stoppedValue_mono` on `-Y`.
-/
lemma supermartingale_stopped_le_initial
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Y : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hY : Supermartingale Y 𝓕 μ)
    {τ : Ω → ℕ} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : ℕ∞)))
    {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue Y (fun ω => (τ ω : ℕ∞)) ω ∂μ ≤ ∫ ω, Y 0 ω ∂μ := by
  -- `-Y` is a submartingale; apply `expected_stoppedValue_mono` with the constant
  -- stopping time `0 ≤ τ`.
  have hnegY : Submartingale (-Y) 𝓕 μ := hY.neg
  have h0 : IsStoppingTime 𝓕 (fun _ : Ω => ((0 : ℕ) : ℕ∞)) := by
    simpa using isStoppingTime_const 𝓕 (0 : ℕ)
  have hle : (fun _ : Ω => ((0 : ℕ) : ℕ∞)) ≤ (fun ω => (τ ω : ℕ∞)) := by
    intro ω
    show ((0 : ℕ) : ℕ∞) ≤ ((τ ω : ℕ) : ℕ∞)
    exact_mod_cast Nat.zero_le _
  have hbdd : ∀ ω, ((τ ω : ℕ∞)) ≤ (N : ℕ∞) := fun ω => by exact_mod_cast hτ_le ω
  have key :=
    hnegY.expected_stoppedValue_mono h0 hτ hle (N := N) hbdd
  -- `stoppedValue (-Y) (fun _ => 0) ω = -Y 0 ω` and `stoppedValue (-Y) τ = -stoppedValue Y τ`.
  have h_untop_zero : (((0 : ℕ) : ℕ∞)).untopA = (0 : ℕ) := rfl
  have hs0 : stoppedValue (-Y) (fun _ : Ω => ((0 : ℕ) : ℕ∞)) = fun ω => -Y 0 ω := by
    funext ω
    show -Y (WithTop.untopA ((((0 : ℕ) : ℕ∞)))) ω = -Y 0 ω
    rw [h_untop_zero]
  have h_untop_coe : ∀ n : ℕ, (((n : ℕ) : ℕ∞)).untopA = n := fun _ => rfl
  have hsτ :
      stoppedValue (-Y) (fun ω => (τ ω : ℕ∞))
        = fun ω => -stoppedValue Y (fun ω => (τ ω : ℕ∞)) ω := by
    funext ω
    show -Y (WithTop.untopA (((τ ω : ℕ) : ℕ∞))) ω =
         -Y (WithTop.untopA (((τ ω : ℕ) : ℕ∞))) ω
    rfl
  rw [hs0, hsτ, integral_neg, integral_neg] at key
  linarith

/-
The event `{∃ t ≤ N, c ≤ Y t ω}` is measurable for an adapted process.
-/
lemma measurableSet_exists_le_and_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Y : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    (hY : Supermartingale Y 𝓕 μ) {c : ℝ} {N : ℕ} :
    MeasurableSet {ω | ∃ t : ℕ, t ≤ N ∧ c ≤ Y t ω} := by
  have h_adapted : ∀ t, Measurable (Y t) := by
    intro t;
    have hYt_meas : StronglyMeasurable (Y t) := by
      have := hY.1 t;
      exact this.mono ( 𝓕.le t );
    exact hYt_meas.measurable;
  simp +decide only [Set.setOf_exists];
  exact MeasurableSet.iUnion fun i => MeasurableSet.inter ( MeasurableSet.const _ ) ( measurableSet_le measurable_const ( h_adapted i ) )

/-
Ville's inequality for non-negative supermartingales:
    `μ{∃ t ≤ N, Y t ω ≥ c} ≤ E[Y 0] / c`.

    Uses `supermartingale_stopped_le_initial` with the hitting time
    `τ_hit := hittingBtwn Y (Set.Ici c) 0 N`. On the event
    `{∃ t ≤ N, Y t ω ≥ c}`, `stoppedValue Y τ_hit ≥ c`
    (by `hittingBtwn_mem_set`). Non-negativity of Y gives
    `∫ stoppedValue Y τ_hit ≥ c * μ.real(event)`. Combining:
    `c * μ.real(event) ≤ ∫ Y 0`, hence the result.
-/
lemma ville_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Y : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hY : Supermartingale Y 𝓕 μ) (hY_nn : ∀ t ω, 0 ≤ Y t ω)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ c ≤ Y t ω} ≤
      ENNReal.ofReal ((∫ ω, Y 0 ω ∂μ) / c) := by
  -- Define the hitting time as a `Ω → ℕ`, then coerce to `ℕ∞` when feeding
  -- stoppedValue / IsStoppingTime.
  set τ₀ : Ω → ℕ := fun ω => hittingBtwn Y (Set.Ici c) 0 N ω with hτ₀_def
  set τ : Ω → ℕ∞ := fun ω => (τ₀ ω : ℕ∞) with hτ_def
  have h_adapted : Adapted 𝓕 Y := hY.1.adapted
  have h_τ_stop : IsStoppingTime 𝓕 τ :=
    h_adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have h_τ_le : ∀ ω, τ₀ ω ≤ N := fun ω => hittingBtwn_le ω
  have h_τ_le' : ∀ ω, τ ω ≤ (N : ℕ∞) := fun ω => by
    show ((τ₀ ω : ℕ) : ℕ∞) ≤ ((N : ℕ) : ℕ∞)
    exact_mod_cast h_τ_le ω
  -- Apply supermartingale_stopped_le_initial to get ∫ stoppedValue Y τ ≤ ∫ Y 0.
  have h_integral_le :
      ∫ ω in {ω | ∃ t ≤ N, c ≤ Y t ω}, stoppedValue Y τ ω ∂μ ≤ ∫ ω, Y 0 ω ∂μ := by
    refine le_trans (MeasureTheory.setIntegral_le_integral ?_ ?_) ?_
    · -- Integrability of `stoppedValue Y τ`.
      have h_integrable : Integrable (stoppedValue (-Y) τ) μ :=
        hY.neg.integrable_stoppedValue h_τ_stop h_τ_le'
      have h_eq : stoppedValue Y τ = fun ω => -stoppedValue (-Y) τ ω := by
        funext ω; simp [stoppedValue]
      rw [h_eq]; exact h_integrable.neg
    · filter_upwards with ω using hY_nn _ _
    · -- `supermartingale_stopped_le_initial` with `τ₀ : Ω → ℕ`. `τ = fun ω => (τ₀ ω : ℕ∞)` by defn.
      exact supermartingale_stopped_le_initial hY (τ := τ₀) h_τ_stop h_τ_le
  -- On the event {ω | ∃ t ≤ N, c ≤ Y t ω}, we have stoppedValue Y τ ω ≥ c.
  have h_stoppedValue_ge_c :
      ∀ ω ∈ {ω | ∃ t ≤ N, c ≤ Y t ω}, c ≤ stoppedValue Y τ ω := by
    intro ω hω
    obtain ⟨t, ht₁, ht₂⟩ := hω
    have h_hit : c ≤ Y (hittingBtwn Y (Set.Ici c) 0 N ω) ω := by
      have : Y (hittingBtwn Y (Set.Ici c) 0 N ω) ω ∈ Set.Ici c :=
        hittingBtwn_mem_set ⟨t, ⟨Nat.zero_le _, ht₁⟩, ht₂⟩
      exact this
    -- `stoppedValue Y τ ω = Y (τ₀ ω).untopA ω = Y (hittingBtwn ...) ω`.
    show Y (WithTop.untopA ((τ₀ ω : ℕ∞))) ω ≥ c
    have h_untop : (WithTop.untopA ((τ₀ ω : ℕ∞)) : ℕ) = τ₀ ω := rfl
    rw [h_untop]
    exact h_hit
  -- Bound the set-integral below by `c * μ(event)`.
  have h_integral_bound :
      c * (μ {ω | ∃ t ≤ N, c ≤ Y t ω}).toReal ≤
        ∫ ω in {ω | ∃ t ≤ N, c ≤ Y t ω}, stoppedValue Y τ ω ∂μ := by
    have h_meas : MeasurableSet {ω | ∃ t : ℕ, t ≤ N ∧ c ≤ Y t ω} :=
      measurableSet_exists_le_and_le hY
    have h_integrableOn :
        IntegrableOn (stoppedValue Y τ) {ω | ∃ t ≤ N, c ≤ Y t ω} μ := by
      have h_integrable : Integrable (stoppedValue (-Y) τ) μ :=
        hY.neg.integrable_stoppedValue h_τ_stop h_τ_le'
      have h_eq : stoppedValue Y τ = fun ω => -stoppedValue (-Y) τ ω := by
        funext ω; simp [stoppedValue]
      rw [h_eq]
      exact h_integrable.neg.integrableOn
    have h_const_integrableOn :
        IntegrableOn (fun _ : Ω => c) {ω | ∃ t ≤ N, c ≤ Y t ω} μ :=
      MeasureTheory.integrableOn_const (μ := μ)
    calc c * (μ {ω | ∃ t ≤ N, c ≤ Y t ω}).toReal
        = ∫ _ in {ω | ∃ t ≤ N, c ≤ Y t ω}, c ∂μ := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm,
              Measure.real]
      _ ≤ ∫ ω in {ω | ∃ t ≤ N, c ≤ Y t ω}, stoppedValue Y τ ω ∂μ :=
          MeasureTheory.setIntegral_mono_on h_const_integrableOn h_integrableOn
            h_meas h_stoppedValue_ge_c
  rw [ENNReal.le_ofReal_iff_toReal_le] <;> norm_num
  · rw [le_div_iff₀' hc]; linarith
  · exact div_nonneg (MeasureTheory.integral_nonneg fun _ => hY_nn _ _) hc.le

/-
**Ville's inequality for a sub-Gaussian martingale.**

    For `N ≥ 1`, `τ > 0`, and a sub-Gaussian martingale `M` starting at 0:
    `μ { ω | ∃ t ≤ N, M_t ω ≥ τ }  ≤  exp(-τ²/(2σ²N))`.

    We assume `M.process 0 = 0` a.s., which is standard in the
    anytime-valid confidence sequence literature (initial wealth = 1,
    log-wealth = 0).
-/
theorem ville_ineq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG σ 𝓕 μ) (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N)
    -- Added hypothesis: process starts at 0 a.s. (standard in anytime-valid CS literature)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * σ^2 * N))) := by
  have h_replace : μ {ω | ∃ t ≤ N, M.process t ω ≥ τ} ≤ μ {ω | ∃ t ≤ N, Real.exp ((τ / (σ ^ 2 * N)) * M.process t ω) / Real.exp ((τ / (σ ^ 2 * N)) ^ 2 * σ ^ 2 * t / 2) ≥ Real.exp ((τ / (σ ^ 2 * N)) * τ - (τ / (σ ^ 2 * N)) ^ 2 * σ ^ 2 * N / 2)} := by
    refine' MeasureTheory.measure_mono fun ω hω => _;
    obtain ⟨ t, ht₁, ht₂ ⟩ := hω; use t, ht₁; rw [ ← Real.exp_sub ] ; gcongr;
  have h_exp_process : Supermartingale (fun t ω => Real.exp ((τ / (σ ^ 2 * N)) * M.process t ω) / Real.exp ((τ / (σ ^ 2 * N)) ^ 2 * σ ^ 2 * t / 2)) 𝓕 μ := by
    convert exp_process_is_supermartingale M ( τ / ( σ ^ 2 * N ) ) ( by positivity ) using 1;
  refine' le_trans h_replace _;
  convert ville_supermartingale h_exp_process _ _ _ using 1;
  · rw [ MeasureTheory.integral_congr_ae ( hM0.mono fun ω hω => by rw [ hω ] ) ] ; norm_num;
    rw [ ← Real.exp_neg ] ; ring;
    grind;
  · exact fun t ω => div_nonneg ( Real.exp_nonneg _ ) ( Real.exp_nonneg _ );
  · positivity

/-! ## Smoke test — the structure type-checks.

A non-vacuous instance needs a concrete filtered probability space
(e.g. an iid sub-Gaussian increment sequence on `(ℝ^ℕ, canonicalFiltration)`).
That construction is Day-2 work once the structure stabilises. For
now this file compiles and exposes the 3-theorem Ville ladder with
sorries at the two steps that need real measure-theoretic work. -/


end Kairos.Stats
