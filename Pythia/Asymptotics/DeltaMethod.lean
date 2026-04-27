/-
Copyright (c) 2025 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia contributors
-/
import Mathlib
import Pythia.Tactic.Pythia

/-!
# Scalar Delta Method

The **delta method** (Mann–Wald 1943; van der Vaart, *Asymptotic Statistics*, 1998, Thm 3.1):
if a sequence of random variables `Tₙ` satisfies `rₙ (Tₙ − θ) →_d Z` for a scaling
sequence `rₙ → +∞`, and `g : ℝ → ℝ` is differentiable at `θ` with derivative `g'(θ)`,
then `rₙ (g(Tₙ) − g(θ)) →_d g'(θ) · Z`.

## Proof strategy

We factor the increment through a *slope function*
`φ(x) = (g(x) − g(θ)) / (x − θ)` (extended to `g'` at `x = θ`),
so that `rₙ (g(Tₙ) − g(θ)) = rₙ (Tₙ − θ) · φ(Tₙ)`.

1. **`Tₙ →_P θ`** from `rₙ(Tₙ − θ) →_d Z` and `rₙ → ∞`, via the Portmanteau theorem.
2. **`φ(Tₙ) →_P g'`** since `φ` is continuous at `θ` (by differentiability) and `Tₙ →_P θ`.
3. **Slutsky + continuous mapping**: `rₙ(Tₙ − θ) · φ(Tₙ) →_d Z · g' = g' · Z`.

## Main declarations

* `Pythia.Asymptotics.delta_method`: the scalar delta method theorem.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Pythia.Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Slope function -/

/-- The slope function associated to `g`, `g'`, `θ`:
`φ(x) = (g(x) − g(θ)) / (x − θ)` for `x ≠ θ`, and `φ(θ) = g'`. -/
noncomputable def slopeFunction (g : ℝ → ℝ) (g' θ : ℝ) : ℝ → ℝ :=
  Function.update (fun x => (g x - g θ) / (x - θ)) θ g'

@[simp]
lemma slopeFunction_self (g : ℝ → ℝ) (g' θ : ℝ) :
    slopeFunction g g' θ θ = g' := by
  simp [slopeFunction]

lemma slopeFunction_of_ne (g : ℝ → ℝ) (g' θ x : ℝ) (hx : x ≠ θ) :
    slopeFunction g g' θ x = (g x - g θ) / (x - θ) := by
  simp [slopeFunction, hx]

lemma slopeFunction_mul_sub (g : ℝ → ℝ) (g' θ x : ℝ) :
    slopeFunction g g' θ x * (x - θ) = g x - g θ := by
  by_cases hx : x = θ
  · simp [hx]
  · rw [slopeFunction_of_ne g g' θ x hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]

lemma slopeFunction_continuousAt {g : ℝ → ℝ} {g' θ : ℝ} (hg : HasDerivAt g g' θ) :
    ContinuousAt (slopeFunction g g' θ) θ := by
  have h_slope : Filter.Tendsto (fun x => (g x - g θ) / (x - θ))
      (nhdsWithin θ {θ}ᶜ) (nhds g') := by
    rw [hasDerivAt_iff_tendsto_slope] at hg
    simpa [div_eq_inv_mul] using hg
  rw [Metric.tendsto_nhdsWithin_nhds] at h_slope
  exact Metric.tendsto_nhds_nhds.mpr fun ε hε => by
    rcases h_slope ε hε with ⟨δ, hδ, H⟩
    exact ⟨δ, hδ, by intro x hx; by_cases h : x = θ <;> unfold slopeFunction <;> aesop⟩

omit [IsProbabilityMeasure μ] in
lemma slopeFunction_measurable {g : ℝ → ℝ} {g' θ : ℝ} (hg_meas : Measurable g) :
    Measurable (slopeFunction g g' θ) := by
  have h_slope_measurable : Measurable (fun x => (g x - g θ) / (x - θ)) :=
    Measurable.mul (hg_meas.sub measurable_const)
      (Measurable.inv (measurable_id.sub measurable_const))
  have h_update_measurable : ∀ {f : ℝ → ℝ} (a b : ℝ), Measurable f →
      Measurable (Function.update f a b) := by
    intro f a b hf
    rw [show Function.update f a b = fun x => if x = a then b else f x by
      ext x; by_cases hx : x = a <;> simp +decide [hx, Function.update_apply]]
    exact Measurable.ite (MeasurableSet.singleton a) measurable_const hf
  exact h_update_measurable _ _ h_slope_measurable

/-! ### Convergence-in-probability helpers -/

/-- If `rₙ → +∞` and `rₙ (Xₙ − c) →_d Z`, then `Xₙ →_P c`.
Uses the Portmanteau theorem (limsup bound for closed sets). -/
lemma tendstoInMeasure_of_tendsto_atTop_mul
    {X : ℕ → Ω → ℝ} {Z : Ω → ℝ} {r : ℕ → ℝ} {c : ℝ}
    (hr : Tendsto r atTop atTop)
    (hXZ : TendstoInDistribution (fun n ω => r n * (X n ω - c)) atTop Z μ)
    (hX : ∀ n, AEMeasurable (X n) μ) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  intro ε hε
  rcases ENNReal.lt_iff_exists_real_btwn.mp hε with ⟨δ, hδ, hδε⟩
  have h_portmanteau : ∀ M > 0, Filter.limsup (fun n => μ {ω | |r n * (X n ω - c)| ≥ M})
      Filter.atTop ≤ μ {ω | |Z ω| ≥ M} := by
    intro M _
    have h_portmanteau : Filter.limsup (fun n => (μ.map (fun ω => r n * (X n ω - c)))
        {x | |x| ≥ M}) Filter.atTop ≤ (μ.map Z) {x | |x| ≥ M} :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hXZ.3
        (isClosed_le continuous_const continuous_abs)
    convert h_portmanteau using 1
    · refine' Filter.limsup_congr _
      filter_upwards [hr.eventually_gt_atTop 0] with n hn
      rw [Measure.map_apply_of_aemeasurable]
      · rfl
      · exact AEMeasurable.const_mul (hX n |> AEMeasurable.sub <| aemeasurable_const) _
      · exact measurableSet_le measurable_const measurable_norm
    · rw [Measure.map_apply_of_aemeasurable]
      · rfl
      · exact hXZ.aemeasurable_limit
      · exact measurableSet_le measurable_const measurable_norm
  have h_r_n_large : ∀ M > 0, ∃ N, ∀ n ≥ N,
      μ {ω | |X n ω - c| ≥ δ} ≤ μ {ω | |r n * (X n ω - c)| ≥ M} := by
    intro M hM_pos
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, |r n| ≥ M / δ :=
      Filter.eventually_atTop.mp (hr.eventually_ge_atTop (M / δ)) |> fun ⟨N, hN⟩ =>
        ⟨N, fun n hn => le_trans (hN n hn) (le_abs_self _)⟩
    use N
    intro n hn
    exact MeasureTheory.measure_mono fun ω hω => by
      have h_abs : |r n * (X n ω - c)| ≥ |r n| * δ := by
        simpa only [abs_mul] using mul_le_mul_of_nonneg_left hω.out (abs_nonneg _)
      exact le_trans (by nlinarith [hN n hn, mul_div_cancel₀ M (show δ ≠ 0 by aesop)]) h_abs
  have h_Z_large : Filter.Tendsto (fun M => μ {ω | |Z ω| ≥ M}) Filter.atTop (nhds 0) := by
    convert MeasureTheory.tendsto_measure_iInter_atTop _ _ _
    · rw [show (⋂ n : ℝ, {ω | |Z ω| ≥ n}) = ∅ from
        Set.eq_empty_of_forall_notMem fun ω hω => by
          rcases exists_nat_gt (|Z ω|) with ⟨n, hn⟩
          exact not_lt_of_ge (Set.mem_iInter.mp hω n) hn]
      norm_num
    · infer_instance
    · have := hXZ.aemeasurable_limit
      exact fun M => this.norm.nullMeasurable measurableSet_Ici
    · exact fun x y hxy => Set.setOf_subset_setOf.2 fun ω hω => le_trans hxy hω
    · exact ⟨0, ne_of_lt (MeasureTheory.measure_lt_top _ _)⟩
  have h_combined : Filter.Tendsto (fun n => μ {ω | |X n ω - c| ≥ δ}) Filter.atTop (nhds 0) := by
    refine' tendsto_order.2 ⟨fun x => _, fun x hx => _⟩
    · aesop
    · obtain ⟨M, hM⟩ : ∃ M > 0, μ {ω | |Z ω| ≥ M} < x := by
        have := h_Z_large.eventually (gt_mem_nhds hx)
        have := this.and (Filter.eventually_gt_atTop 0)
        obtain ⟨M, hM₁, hM₂⟩ := this.exists
        exact ⟨M, hM₂, hM₁⟩
      obtain ⟨N, hN⟩ := h_r_n_large M hM.1
      have := h_portmanteau M hM.1
      rw [Filter.limsup_eq] at this
      simp +zetaDelta at *
      contrapose! this
      refine' lt_of_lt_of_le hM.2 (le_csInf _ _)
      · exact ⟨_, ⟨N, fun n hn => MeasureTheory.measure_mono (Set.subset_univ _)⟩⟩
      · rintro _ ⟨N', hN'⟩
        obtain ⟨n, hn₁, hn₂⟩ := this (Max.max N N')
        exact hn₂.trans (hN n (le_trans (le_max_left _ _) hn₁) |> le_trans <|
          hN' n (le_trans (le_max_right _ _) hn₁))
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_combined _ _
  · exact Filter.Eventually.of_forall fun n => zero_le _
  · simp_all +decide [edist_dist, Real.dist_eq]
    exact ⟨0, fun n _ => MeasureTheory.measure_mono fun x hx => by
      simpa [ENNReal.ofReal_le_ofReal_iff hδ] using le_trans hδε.2.le hx⟩

omit [IsProbabilityMeasure μ] in
/-- If `f` is continuous at `c` and `Xₙ →_P c`, then `f ∘ Xₙ →_P f(c)`. -/
lemma tendstoInMeasure_comp_of_continuousAt
    {X : ℕ → Ω → ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hf_cont : ContinuousAt f c)
    (hX_conv : TendstoInMeasure μ X atTop (fun _ => c))
    (_hX_meas : ∀ n, AEMeasurable (X n) μ)
    (_hf_meas : Measurable f) :
    TendstoInMeasure μ (fun n => f ∘ X n) atTop (fun _ => f c) := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x, |x - c| < δ → edist (f x) (f c) < ε := by
    simpa using Metric.mem_nhds_iff.mp (hf_cont.tendsto.eventually (Metric.eball_mem_nhds _ hε))
  have h_measure_zero : Filter.Tendsto (fun n => μ {ω | δ ≤ |X n ω - c|}) Filter.atTop
      (nhds 0) := by
    have := hX_conv (ENNReal.ofReal δ)
    simp_all +decide [edist_dist, Real.dist_eq]
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_measure_zero _ _
  · exact fun _ => zero_le _
  · exact fun n => MeasureTheory.measure_mono fun x hx =>
      not_lt.1 fun contra => not_le.2 (hδ _ contra) hx

/-! ### Delta method -/

/-- **Delta Method** (scalar case).

If `rₙ (Tₙ − θ) →_d Z` with `rₙ → +∞`, and `g` is differentiable at `θ` with
derivative `g'`, then `rₙ (g(Tₙ) − g(θ)) →_d g' · Z`.

This is Theorem 3.1 of van der Vaart, *Asymptotic Statistics* (1998),
originally due to Mann–Wald (1943).  The proof factors the increment through a
slope function and applies Slutsky's lemma
(`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`). -/
@[stat_lemma]
theorem delta_method
    {T : ℕ → Ω → ℝ} {Z : Ω → ℝ} {r : ℕ → ℝ} {θ g' : ℝ} {g : ℝ → ℝ}
    (hg : HasDerivAt g g' θ)
    (hr : Tendsto r atTop atTop)
    (hTZ : TendstoInDistribution (fun n ω => r n * (T n ω - θ)) atTop Z μ)
    (hT : ∀ n, AEMeasurable (T n) μ)
    (hg_meas : Measurable g) :
    TendstoInDistribution
      (fun n ω => r n * (g (T n ω) - g θ))
      atTop (fun ω => g' * Z ω) μ := by
  -- Factor: rₙ(g(Tₙ) - g(θ)) = rₙ(Tₙ - θ) · φ(Tₙ), then apply Slutsky.
  have h_slope : TendstoInDistribution
      (fun n ω => (r n * (T n ω - θ)) * (slopeFunction g g' θ (T n ω)))
      atTop (fun ω => g' * Z ω) μ := by
    have h_phi : TendstoInMeasure μ (fun n => slopeFunction g g' θ ∘ T n)
        atTop (fun _ => g') := by
      convert tendstoInMeasure_comp_of_continuousAt (slopeFunction_continuousAt hg)
        (tendstoInMeasure_of_tendsto_atTop_mul hr hTZ hT) hT (slopeFunction_measurable hg_meas)
      exact (slopeFunction_self g g' θ).symm
    convert TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
      continuous_mul hTZ h_phi
      (fun n => (slopeFunction_measurable hg_meas).comp_aemeasurable (hT n)) using 1
    simp +decide [mul_comm]
  convert h_slope using 3
  rw [mul_assoc, ← slopeFunction_mul_sub]
  rw [mul_comm (T _ _ - θ)]

end Pythia.Asymptotics
