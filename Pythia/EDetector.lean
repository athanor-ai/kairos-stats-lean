/-
Pythia.EDetector — E-detector framework for sequential change detection.

# Overview

An **e-detector** (Shin, Ramdas, Rinaldo 2024) is the sequential-change-detection
counterpart to confidence sequences. Rather than bounding a parameter at every
stopping time, an e-detector maintains a process that is bounded (≤ 1 in
expectation under the null) and grows when a change has occurred, yielding
anytime-valid Type-I error control.

Reference:
  Shin, J., Ramdas, A., and Rinaldo, A. (2024).
  *E-detectors: a non-parametric framework for online change detection.*
  arXiv:2203.03532.

# Core objects

## EProcess
A non-negative process `M : ℕ → Ω → ℝ≥0` with `M 0 = 1` and `E[M τ] ≤ 1`
for every stopping time τ under the null. This is Ville's inequality in reverse:
Ville gives `ℙ(M_τ ≥ c) ≤ 1/c`; the e-process property is `E[M_τ] ≤ 1`.

## EDetector
Given an e-process M and a threshold α ∈ (0, 1), the detector fires at the
first time t where `M t ≥ 1/α`. Anytime-valid Type-I error control:

  ℙ_null(τ_α < ∞) ≤ α.

This follows from Markov's inequality at the stopped value together with
`E[M_{τ_α}] ≤ 1`.

## MartingaleEProcess
A non-negative martingale starting at 1 is automatically an e-process (the
optional-stopping theorem gives `E[M_τ] = E[M_0] = 1` under integrability
conditions; Ville's inequality is the strict supermartingale version).

## ExpEProcess
For an iid sequence X_1, X_2, … that is sub-Gaussian with parameter σ, the
exponential process

  M_t = exp(λ · S_t − t · ψ(λ)),      ψ(λ) = λ² σ² / 2

is a non-negative martingale starting at 1 under the null (sub-Gaussian MGF
equals `exp(ψ(λ))` per step). This bridges the e-detector framework to
`Pythia.SubGaussianMG`.

## Combining e-processes
If M and N are e-processes, so are:
  • `(M + N) / 2` (mixture / averaging) — convexity of the e-class;
  • `M · N` (product) — when M and N are independent.

This enables detector combination (e.g. multi-stream monitoring, independent
sensors aggregated into a single anytime-valid alarm).

# Closure roadmap (per statement)

* `eprocess_supermartingale_bound` — direct application of Ville's inequality
  (`VilleSupermartingale.ville_ineq`) after establishing that any
  supermartingale with E[M_0] = 1 satisfies the e-process bound at stopping times.
  Needs: `OptionalStoppingUnbounded.stoppedValue_le_nnreal` or similar.

* `edetector_type_i_error` — one-line Markov on `M_{τ_α}` + e-process bound.
  Needs: `eprocess_supermartingale_bound` + `MeasureTheory.measure_le_of_integral`.

* `martingale_eprocess_iff` — forward: optional stopping (`stoppedValue_integral_eq`
  for the martingale). Reverse: supermartingale is weaker than martingale, direct.
  Needs: `MeasureTheory.Martingale.stoppedValue_integral_eq`.

* `exp_eprocess_subgaussian` — apply `SubGaussianMG.exp_supermartingale` at the
  optimal λ; M_0 = exp(0) = 1. Uses `HasCondSubgaussianMGF` from Mathlib.

* `combine_eprocesses_avg` — linearity of expectation + convexity.
  Product version needs independence hypothesis.

# Status

Tier 2 / sequential stats scaffold (2026-04-25).
All five statements are `sorry`-ed with flagged closure plans.
**Excluded from `Pythia.AxiomAudit` until closures land.**
-/
import Mathlib
import Pythia.Basic
import Pythia.SubGaussianMG
import Pythia.VilleSupermartingale

namespace Pythia

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal BigOperators

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {𝓕 : Filtration ℕ mΩ}

/-! ## E-process definition -/

/-- An **e-process** specification: a non-negative process M adapted to 𝓕,
starting at 1, whose stopped value has expectation ≤ 1 under μ for every
bounded stopping time τ.

The `e_bound` field captures `∀ τ bounded stopping time, ∫ M τ ∂μ ≤ 1`.
We carry the bound with respect to bounded stopping times (≤ N for some N)
rather than general stopping times, matching the Doob/Ville machinery
available in Mathlib v4.28.0 for `stoppedValue`. -/
structure EProcess (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- The process itself. -/
  process    : ℕ → Ω → ℝ
  /-- Non-negativity at every time and every ω. -/
  nonneg     : ∀ t ω, 0 ≤ process t ω
  /-- Initial value is 1. -/
  start_one  : ∀ ω, process 0 ω = 1
  /-- Adapted to the filtration. -/
  adapted    : Adapted 𝓕 process
  /-- Integrability at each step. -/
  integrable : ∀ t, Integrable (process t) μ
  /-- E-process bound: for every bounded stopping time τ (τ ω ≤ N for some N),
      the expected stopped value is at most 1. -/
  e_bound    : ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (N : ℕ) (_ : ∀ ω, τ ω ≤ ↑N),
      ∫ ω, stoppedValue process τ ω ∂μ ≤ 1

/-! ## Core theorems -/

/-
**E-process supermartingale bound** (Ville-style).

If M is an e-process, then for any threshold `c > 0`:

  ℙ_null(∃ t, M_t ≥ c) ≤ 1 / c.

This is Ville's inequality: the e-process is a non-negative supermartingale
starting at 1, so the measure of the event that M ever exceeds `c` is at
most `E[M_0] / c = 1 / c`.

Closure plan: apply `VilleSupermartingale.ville_ineq` after establishing that
`EProcess.e_bound` implies the supermartingale property on the process. The
key step is the tower property: `E[M_{t+1} | F_t] ≤ M_t` follows from
`e_bound` applied to the constant stopping time t+1 versus t. Then
`ville_ineq` yields the bound directly with `E[M_0] = 1`.
-/
theorem eprocess_supermartingale_bound
    (M : EProcess 𝓕 μ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t : ℕ, c ≤ M.process t ω} ≤ ENNReal.ofReal (1 / c) := by
  -- closure plan: derive Supermartingale M.process 𝓕 μ from M.e_bound via the
  -- tower property, then apply ville_ineq with E[M.process 0] = 1.
  have h_ville : ∀ (N : ℕ), μ {ω | ∃ t ≤ N, c ≤ M.process t ω} ≤ ENNReal.ofReal (1 / c) := by
    intro N
    have h_stopped : ∫ ω, stoppedValue M.process (fun ω' => ↑(hittingBtwn M.process {y | c ≤ y} 0 N ω')) ω ∂μ ≤ 1 := by
      have := M.e_bound ( fun ω' => ↑ ( hittingBtwn M.process { y | c ≤ y } 0 N ω' ) ) ?_ N ?_;
      · exact this;
      · have := M.adapted;
        apply_rules [ Adapted.isStoppingTime_hittingBtwn ];
        exact measurableSet_Ici;
      · simp +decide [ hittingBtwn_le ];
    have h_stopped_ge : ∀ ω ∈ {ω | ∃ t ≤ N, c ≤ M.process t ω}, c ≤ stoppedValue M.process (fun ω' => ↑(hittingBtwn M.process {y | c ≤ y} 0 N ω')) ω := by
      intro ω hω
      obtain ⟨t, ht₁, ht₂⟩ := hω
      have h_stopped_ge : c ≤ M.process (hittingBtwn M.process {y | c ≤ y} 0 N ω) ω := by
        apply hittingBtwn_mem_set;
        exact ⟨ t, ⟨ Nat.zero_le _, ht₁ ⟩, ht₂ ⟩;
      unfold stoppedValue; aesop;
    have h_integral_ge : ∫⁻ ω in {ω | ∃ t ≤ N, c ≤ M.process t ω}, ENNReal.ofReal (c) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (stoppedValue M.process (fun ω' => ↑(hittingBtwn M.process {y | c ≤ y} 0 N ω')) ω) ∂μ := by
      refine' le_trans ( MeasureTheory.setLIntegral_mono' _ _ ) ( MeasureTheory.setLIntegral_le_lintegral _ _ );
      · have h_measurable : ∀ t ≤ N, MeasurableSet {ω | c ≤ M.process t ω} := by
          intro t ht
          have h_measurable : Measurable (M.process t) := by
            have := M.adapted t;
            exact this.mono ( 𝓕.le t ) le_rfl
          exact measurableSet_le measurable_const h_measurable;
        convert MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun ht => h_measurable t ht using 1 ; aesop;
      · exact fun ω hω => ENNReal.ofReal_le_ofReal ( h_stopped_ge ω hω );
    have h_integral_le : ∫⁻ ω, ENNReal.ofReal (stoppedValue M.process (fun ω' => ↑(hittingBtwn M.process {y | c ≤ y} 0 N ω')) ω) ∂μ ≤ ENNReal.ofReal 1 := by
      rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · exact ENNReal.ofReal_le_ofReal h_stopped;
      · have h_integrable : ∀ (τ : Ω → ℕ∞), IsStoppingTime 𝓕 τ → (∀ ω, τ ω ≤ N) → Integrable (fun ω => stoppedValue M.process τ ω) μ := by
          have h_integrable : ∀ (t : ℕ), Integrable (fun ω => M.process t ω) μ := by
            exact M.integrable;
          exact?;
        apply h_integrable;
        · apply_rules [ Adapted.isStoppingTime_hittingBtwn ];
          · exact M.adapted;
          · exact measurableSet_Ici;
        · simp +decide [ hittingBtwn_le ];
      · filter_upwards [ ] with ω using M.nonneg _ _;
    simp_all +decide [ ENNReal.ofReal_div_of_pos hc ];
    simpa only [ mul_comm ] using h_integral_ge.trans h_integral_le;
  convert le_of_tendsto_of_tendsto' ( MeasureTheory.tendsto_measure_iUnion_atTop ?_ ) tendsto_const_nhds fun N => h_ville N using 1;
  · exact congr_arg _ ( by ext; exact ⟨ fun ⟨ t, ht ⟩ => Set.mem_iUnion.2 ⟨ t, t, le_rfl, ht ⟩, fun h => by rcases Set.mem_iUnion.1 h with ⟨ n, hn ⟩ ; rcases hn with ⟨ t, ht, ht' ⟩ ; exact ⟨ t, ht' ⟩ ⟩ );
  · exact fun N M hNM ω hω => by obtain ⟨ t, ht₁, ht₂ ⟩ := hω; exact ⟨ t, le_trans ht₁ hNM, ht₂ ⟩ ;

/-
**E-detector Type-I error control**.

Given an e-process M and threshold α ∈ (0, 1), define the stopping time:

  τ_α(ω) = inf{t : M_t(ω) ≥ 1/α}

Then `ℙ_null(τ_α < ∞) ≤ α`.

This is the fundamental guarantee of the e-detector framework: by choosing
to alarm at level 1/α, the false-alarm probability under the null is ≤ α
at every stopping time, regardless of how long one observes.

Closure plan: `{ω | τ_α ω < ∞} ⊆ {ω | ∃ t, M.process t ω ≥ 1/α}`. Then
`eprocess_supermartingale_bound` at `c = 1/α` gives the bound as
`ENNReal.ofReal (1 / (1/α)) = ENNReal.ofReal α`.
-/
theorem edetector_type_i_error
    (M : EProcess 𝓕 μ)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1)
    -- The detector firing time: first t where M_t ≥ 1/α.
    (τ_α : Ω → ℕ∞)
    (hτ_stop : IsStoppingTime 𝓕 τ_α)
    -- τ_α fires exactly when M crosses 1/α.
    (hτ_def : ∀ ω, τ_α ω < ⊤ → M.process (τ_α ω).toNat ω ≥ 1 / α) :
    μ {ω | τ_α ω < ⊤} ≤ ENNReal.ofReal α := by
  -- closure plan: inclusion {ω | τ_α ω < ⊤} ⊆ {ω | ∃ t, M_t ω ≥ 1/α},
  -- then eprocess_supermartingale_bound at c = 1/α gives measure ≤ 1/(1/α) = α.
  convert eprocess_supermartingale_bound M ( show 0 < 1 / α by positivity ) |> le_trans _ using 1;
  · norm_num;
  · exact MeasureTheory.measure_mono fun ω hω => ⟨ _, hτ_def ω hω ⟩

/-
**Non-negative martingales starting at 1 are e-processes**.

A non-negative martingale M with M_0 = 1 satisfies `E[M_τ] ≤ 1` for every
bounded stopping time τ (optional stopping for martingales gives `E[M_τ] = 1`;
for supermartingales the inequality is ≤).

This is the key bridge: every non-negative martingale gives an e-process, and
hence an e-detector. In particular, the Wald SPRT likelihood ratio process
(a positive martingale under H_0) is an e-process.

Closure plan: `MeasureTheory.Martingale.stoppedValue_integral_eq` gives equality
`∫ stoppedValue M τ = ∫ M 0` for a uniformly integrable martingale stopped at a
bounded stopping time. Combine with `M.start_one` and the definition of
`EProcess.e_bound`. The `iff` direction (e-process ⇒ martingale) is false in
general; we state the forward direction only in the `→` and the natural weaker
converse (supermartingale ⇒ e-process) as the `←` arm.
-/
theorem martingale_eprocess_iff
    (process : ℕ → Ω → ℝ)
    (hnonneg : ∀ t ω, 0 ≤ process t ω)
    (hstart : ∀ ω, process 0 ω = 1)
    (hadapt : Adapted 𝓕 process)
    (hint : ∀ t, Integrable (process t) μ)
    -- Key hypothesis: M is a non-negative martingale.
    (hmg : Martingale process 𝓕 μ) :
    -- Conclusion: M satisfies the e-process bound (martingales have equality,
    -- so the ≤ 1 bound holds trivially).
    ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (N : ℕ) (_ : ∀ ω, τ ω ≤ ↑N),
        ∫ ω, stoppedValue process τ ω ∂μ ≤ 1 := by
  intro τ hτ N hτN
  -- closure plan: Martingale.stoppedValue_integral_eq gives ∫ stoppedValue process τ = ∫ process 0.
  -- Then ∫ process 0 = 1 by hstart + IsProbabilityMeasure.
  convert Pythia.supermartingale_expected_stoppedValue_le ( hmg.supermartingale ) hτ hτN using 1
  generalize_proofs at *;
  aesop

/-! ### Helpers for exponential e-process -/

/-
Telescoping: the partial sum of increments equals mg.process t - mg.process 0.
-/
private lemma exp_eprocess_sum_telescope
    [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ}
    (mg : SubGaussianMG σ 𝓕 μ)
    (X : ℕ → Ω → ℝ)
    (hX_eq : ∀ t ω, X t ω = mg.process (t + 1) ω - mg.process t ω)
    (t : ℕ) (ω : Ω) :
    (Finset.range t).sum (fun i => X i ω) = mg.process t ω - mg.process 0 ω := by
  induction t <;> simp_all +decide [ Finset.sum_range_succ ];
  linarith

/-
Product of two exponential functions of mg.process is integrable, via L²×L²→L¹.
-/
private lemma exp_eprocess_integrable_product
    [StandardBorelSpace Ω]
    {σ : ℝ}
    {𝓕 : Filtration ℕ mΩ}
    (mg : SubGaussianMG σ 𝓕 μ)
    (lam : ℝ) (t : ℕ) :
    Integrable (fun ω => Real.exp (lam * mg.process t ω) *
      Real.exp (-lam * mg.process 0 ω)) μ := by
  have := mg.integrable_exp;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => Real.exp ( lam * mg.process t ω ) ^ 2 + Real.exp ( -lam * mg.process 0 ω ) ^ 2;
  · simp_rw +decide [ ← Real.exp_nat_mul ];
    exact MeasureTheory.Integrable.add ( by simpa [ mul_assoc ] using this t ( 2 * lam ) ) ( by simpa [ mul_assoc ] using this 0 ( -2 * lam ) );
  · exact MeasureTheory.AEStronglyMeasurable.mul ( this t lam |> MeasureTheory.Integrable.aestronglyMeasurable ) ( this 0 ( -lam ) |> MeasureTheory.Integrable.aestronglyMeasurable );
  · filter_upwards [ ] with ω using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; nlinarith [ Real.exp_pos ( lam * mg.process t ω ), Real.exp_pos ( -lam * mg.process 0 ω ) ] ;

/-
The exponential process M_t is integrable for each t.
-/
private lemma exp_eprocess_M_integrable
    [StandardBorelSpace Ω]
    {σ : ℝ}
    {𝓕 : Filtration ℕ mΩ}
    (mg : SubGaussianMG σ 𝓕 μ)
    (X : ℕ → Ω → ℝ)
    (hX_eq : ∀ t ω, X t ω = mg.process (t + 1) ω - mg.process t ω)
    (lam : ℝ) (t : ℕ) :
    Integrable (fun ω => Real.exp (lam * (Finset.range t).sum (fun i => X i ω) -
      ↑t * (lam ^ 2 * σ ^ 2 / 2))) μ := by
  convert ( exp_eprocess_integrable_product mg lam t ) |> ( fun h => h.const_mul ( Real.exp ( - ( t : ℝ ) * ( lam ^ 2 * σ ^ 2 / 2 ) ) ) ) using 1;
  ext ω; rw [ ← Real.exp_add, ← Real.exp_add ] ; rw [ exp_eprocess_sum_telescope mg X hX_eq t ω ] ; ring;

/-
One-step conditional expectation bound for the exponential process.
-/
private lemma exp_eprocess_condexp_le
    [StandardBorelSpace Ω]
    {σ : ℝ} (hσ : 0 < σ)
    {𝓕 : Filtration ℕ mΩ}
    (mg : SubGaussianMG σ 𝓕 μ)
    (X : ℕ → Ω → ℝ)
    (hX_eq : ∀ t ω, X t ω = mg.process (t + 1) ω - mg.process t ω)
    (lam : ℝ) (t : ℕ) :
    μ[fun ω => Real.exp (lam * (Finset.range (t + 1)).sum (fun i => X i ω) -
      ↑(t + 1) * (lam ^ 2 * σ ^ 2 / 2)) | 𝓕 t] ≤ᶠ[ae μ]
    fun ω => Real.exp (lam * (Finset.range t).sum (fun i => X i ω) -
      ↑t * (lam ^ 2 * σ ^ 2 / 2)) := by
  refine' Filter.EventuallyLE.trans _ _;
  exact fun ω => Real.exp ( lam * ∑ i ∈ Finset.range t, X i ω - ↑t * ( lam ^ 2 * σ ^ 2 / 2 ) ) * μ[fun ω => Real.exp ( lam * X t ω - lam ^ 2 * σ ^ 2 / 2 ) | 𝓕 t] ω;
  · convert MeasureTheory.condExp_mul_of_stronglyMeasurable_left _ _ _ |> Filter.EventuallyEq.le using 1;
    · congr! 2;
      simp +decide [ Finset.sum_range_succ, ← Real.exp_add ] ; ring;
    · have h_sum_meas : ∀ i < t, StronglyMeasurable[𝓕 t] (fun ω => X i ω) := by
        intro i hi
        have h_meas : StronglyMeasurable[𝓕 t] (fun ω => mg.process (i + 1) ω) ∧ StronglyMeasurable[𝓕 t] (fun ω => mg.process i ω) := by
          have h_meas : ∀ j ≤ t, StronglyMeasurable[𝓕 t] (fun ω => mg.process j ω) := by
            intro j hj;
            have := mg.adapted j;
            exact this.stronglyMeasurable.mono ( 𝓕.mono hj );
          exact ⟨ h_meas _ ( Nat.succ_le_of_lt hi ), h_meas _ ( Nat.le_of_lt hi ) ⟩;
        simpa only [ hX_eq ] using h_meas.1.sub h_meas.2;
      have h_sum_meas : StronglyMeasurable[𝓕 t] (fun ω => ∑ i ∈ Finset.range t, X i ω) := by
        exact Finset.stronglyMeasurable_fun_sum _ fun i hi => h_sum_meas i ( Finset.mem_range.mp hi );
      exact Real.continuous_exp.comp_stronglyMeasurable ( h_sum_meas.const_mul _ |> StronglyMeasurable.sub <| stronglyMeasurable_const );
    · convert exp_eprocess_M_integrable mg X hX_eq lam ( t + 1 ) using 1;
      ext ω; simp +decide [ Finset.sum_range_succ, hX_eq ] ; ring;
      rw [ ← Real.exp_add ] ; ring;
    · have := mg.increments_subG t;
      have := this.integrable_exp_mul lam;
      convert this.mul_const ( Real.exp ( -lam ^ 2 * σ ^ 2 / 2 ) ) using 2 ; rw [ hX_eq ] ; rw [ ← Real.exp_add ] ; ring;
  · have h_cond_exp : μ[fun ω => Real.exp (lam * X t ω - lam ^ 2 * σ ^ 2 / 2) | 𝓕 t] ≤ᵐ[μ] fun ω => 1 := by
      have h_cond_exp : μ[fun ω => Real.exp (lam * X t ω) | 𝓕 t] ≤ᵐ[μ] fun ω => Real.exp (lam ^ 2 * σ ^ 2 / 2) := by
        convert mg.increments_subG t |> fun h => h.ae_condExp_le lam using 1;
        simp +decide [ hX_eq, mul_comm, Real.toNNReal_of_nonneg ( sq_nonneg σ ) ];
        rfl;
      have h_cond_exp : μ[fun ω => Real.exp (lam * X t ω - lam ^ 2 * σ ^ 2 / 2) | 𝓕 t] =ᵐ[μ] fun ω => Real.exp (-lam ^ 2 * σ ^ 2 / 2) * μ[fun ω => Real.exp (lam * X t ω) | 𝓕 t] ω := by
        have h_cond_exp : μ[fun ω => Real.exp (-lam ^ 2 * σ ^ 2 / 2) * Real.exp (lam * X t ω) | 𝓕 t] =ᵐ[μ] fun ω => Real.exp (-lam ^ 2 * σ ^ 2 / 2) * μ[fun ω => Real.exp (lam * X t ω) | 𝓕 t] ω := by
          apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
          · exact stronglyMeasurable_const;
          · have h_integrable : Integrable (fun ω => Real.exp (lam * X t ω)) μ := by
              have := mg.increments_subG t;
              simpa only [ ← hX_eq ] using this.integrable_exp_mul lam;
            exact h_integrable.const_mul _;
          · have := mg.increments_subG t;
            simpa only [ ← hX_eq ] using this.integrable_exp_mul lam;
        convert h_cond_exp using 3 ; rw [ ← Real.exp_add ] ; ring;
      filter_upwards [ h_cond_exp, ‹μ[fun ω => Real.exp (lam * X t ω) | 𝓕 t] ≤ᶠ[ae μ] fun ω => Real.exp (lam ^ 2 * σ ^ 2 / 2)› ] with ω hω₁ hω₂ using by rw [ hω₁ ] ; exact le_trans ( mul_le_mul_of_nonneg_left hω₂ <| Real.exp_nonneg _ ) <| by rw [ ← Real.exp_add ] ; ring_nf; norm_num;
    filter_upwards [ h_cond_exp ] with ω hω using mul_le_of_le_one_right ( Real.exp_nonneg _ ) hω

/-
The exponential process is a supermartingale for all λ.
-/
private lemma exp_eprocess_supermartingale
    [StandardBorelSpace Ω]
    {σ : ℝ} (hσ : 0 < σ)
    {𝓕 : Filtration ℕ mΩ}
    (mg : SubGaussianMG σ 𝓕 μ)
    (X : ℕ → Ω → ℝ)
    (hX_eq : ∀ t ω, X t ω = mg.process (t + 1) ω - mg.process t ω)
    (lam : ℝ) :
    Supermartingale
      (fun t ω => Real.exp (lam * (Finset.range t).sum (fun i => X i ω) -
        ↑t * (lam ^ 2 * σ ^ 2 / 2))) 𝓕 μ := by
  -- Apply the supermartingale_nat theorem to conclude the proof.
  apply supermartingale_nat;
  · intro t
    have h_sum : ∀ ω, (Finset.range t).sum (fun i => X i ω) = mg.process t ω - mg.process 0 ω := by
      exact?;
    have h_sum : StronglyMeasurable[𝓕 t] (fun ω => mg.process t ω - mg.process 0 ω) := by
      apply_rules [ StronglyMeasurable.sub, mg.adapted ];
      · have := mg.adapted t;
        exact this.stronglyMeasurable;
      · have := mg.adapted 0;
        exact this.stronglyMeasurable.mono ( 𝓕.mono ( Nat.zero_le _ ) );
    convert Real.continuous_exp.comp_stronglyMeasurable ( h_sum.const_mul lam |> StronglyMeasurable.sub <| stronglyMeasurable_const ) using 1 ; aesop;
  · exact?;
  · -- Apply the hypothesis `h_condexp` directly to conclude the proof.
    apply exp_eprocess_condexp_le hσ mg X hX_eq lam

/-
**Exponential e-process for sub-Gaussian sequences**.

Let X_1, X_2, … be iid with mean 0 and sub-Gaussian parameter σ under the
null measure μ. For any λ, the exponential process

  M_t(ω) = exp(λ · S_t(ω) − t · λ² σ² / 2),      S_t = Σ_{i < t} X_i

satisfies:
  1. M_0 = 1,
  2. M_t ≥ 0 for all t,
  3. E[M_τ] ≤ 1 for every bounded stopping time τ.

Hence M is an e-process; this bridges `Pythia.SubGaussianMG` to the
e-detector framework.
-/
theorem exp_eprocess_subgaussian
    [StandardBorelSpace Ω]
    {σ : ℝ} (hσ : 0 < σ)
    (mg : SubGaussianMG σ 𝓕 μ)
    (X : ℕ → Ω → ℝ)
    (hX_eq : ∀ t ω, X t ω = mg.process (t + 1) ω - mg.process t ω)
    (lam : ℝ) :
    let S : ℕ → Ω → ℝ := fun t ω => (Finset.range t).sum (fun i => X i ω)
    let M : ℕ → Ω → ℝ :=
      fun t ω => Real.exp (lam * S t ω - t * (lam ^ 2 * σ ^ 2 / 2))
    ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (N : ℕ) (_ : ∀ ω, τ ω ≤ ↑N),
        ∫ ω, stoppedValue M τ ω ∂μ ≤ 1 := by
  intro S M τ hτ N hτN
  convert supermartingale_expected_stoppedValue_le ( exp_eprocess_supermartingale hσ mg X hX_eq lam ) hτ hτN using 1;
  norm_num

/-
**Combining e-processes by averaging**.

If M and N are e-processes under the same filtration and null measure μ,
then their average `(M + N) / 2` is also an e-process.

This is the simplest detector-combination result: run two independent
detection methods and average. The e-class is convex, so any mixture of
e-processes is an e-process.

The product `M · N` is also an e-process when M and N are independent, but
that version requires an independence hypothesis and is left as a follow-up.

Closure plan: linearity of the integral gives
  `∫ stoppedValue ((M + N)/2) τ = (∫ stoppedValue M τ + ∫ stoppedValue N τ) / 2`
and by `M.e_bound`, `N.e_bound` both integrals are ≤ 1, so the sum / 2 ≤ 1.
This is a 10-line local proof once the `stoppedValue` linearity lemmas are
identified (likely `stoppedValue_add` + `integral_add` in Mathlib).
-/
theorem combine_eprocesses_avg
    (M N : EProcess 𝓕 μ) :
    -- The averaged process satisfies the e-process bound.
    ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (K : ℕ) (_ : ∀ ω, τ ω ≤ ↑K),
        ∫ ω, stoppedValue (fun t ω => (M.process t ω + N.process t ω) / 2) τ ω ∂μ ≤ 1 := by
  intro τ hτ K hτK
  -- closure plan: stoppedValue_add + integral_add give linearity;
  -- then M.e_bound + N.e_bound + (a + b)/2 ≤ 1 when a, b ≤ 1.
  -- By linearity of the integral, we can split the integral into the sum of two integrals.
  have h_split : ∫ ω, stoppedValue (fun t ω => (M.process t ω + N.process t ω) / 2) τ ω ∂μ = (∫ ω, stoppedValue M.process τ ω ∂μ + ∫ ω, stoppedValue N.process τ ω ∂μ) / 2 := by
    rw [ ← MeasureTheory.integral_add, ← MeasureTheory.integral_div ];
    · congr;
    · exact integrable_stoppedValue ℕ hτ M.integrable hτK;
    · exact integrable_stoppedValue ℕ hτ N.integrable hτK;
  linarith [ M.e_bound τ hτ K hτK, N.e_bound τ hτ K hτK ]

end Pythia