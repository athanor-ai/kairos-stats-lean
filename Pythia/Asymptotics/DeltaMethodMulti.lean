/-
Copyright (c) 2026 Pythia Contributors.
All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Pythia.Tactic.Pythia

/-!
# Multivariate Delta Method

This file proves the **multivariate delta method** (van der Vaart,
*Asymptotic Statistics*, 1998, Theorem 3.1):

> If `√n (Tₙ − θ) →_d Z` in a normed space `E` and `g : E → F` is Fréchet
> differentiable at `θ` with derivative `J`, then
> `√n (g(Tₙ) − g(θ)) →_d J ∘ Z`.

The proof decomposes `g(Tₙ) − g(θ)` via first-order Taylor linearisation into
the linear part `J(Tₙ − θ)` plus a remainder that is `o(‖Tₙ − θ‖)`.
The **continuous mapping theorem** transforms the linear part, and the scaled
remainder vanishes in probability by a tightness + little-o argument, so
**Slutsky's lemma** (`tendstoInDistribution_of_tendstoInMeasure_sub`) closes the
proof.

## Main results

* `Pythia.DeltaMethod.multivariate_delta_method` – the multivariate delta method.
* `Pythia.DeltaMethod.scaled_remainder_tendstoInMeasure` – the key auxiliary
  result: the scaled Taylor remainder converges to zero in probability.

## Practical relevance

Every confidence interval or hypothesis test on a nonlinear function of an
estimator (odds ratios, implied volatility, GMM test statistics, …) relies on
the delta method to convert the estimator's asymptotic normality into an
asymptotic distribution for the transformed quantity.

## References

* van der Vaart, A.W. *Asymptotic Statistics*. Cambridge University Press,
  1998, Theorem 3.1.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Pythia.DeltaMethod

/-- Abbreviation for `√n` as a real number, to avoid coercion headaches. -/
abbrev sqrtN (n : ℕ) : ℝ := Real.sqrt n

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-! ### Helper lemmas -/

/-
From `HasFDerivAt`, for any `c > 0` there exists `δ > 0` such that
`‖x − θ‖ < δ` implies `‖g(x) − g(θ) − J(x − θ)‖ ≤ c * ‖x − θ‖`.
-/
theorem hasFDerivAt_remainder_bound
    {g : E → F} {J : E →L[ℝ] F} {θ : E}
    (hderiv : HasFDerivAt g J θ) (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ x, ‖x - θ‖ < δ → ‖g x - g θ - J (x - θ)‖ ≤ c * ‖x - θ‖ := by
  have := hderiv.isLittleO.bound hc;
  rcases Metric.mem_nhds_iff.mp this with ⟨ δ, δpos, hδ ⟩;
  exact ⟨ δ, δpos, fun x hx => hδ <| mem_ball_iff_norm.mpr hx ⟩

/-
Tightness bound from convergence in distribution: for any `M > 0`, the
limsup of `μ {ω | M ≤ ‖Xₙ ω‖}` is controlled by `μ.map Z {x | M ≤ ‖x‖}`.

This is a consequence of the portmanteau theorem for the closed set
`{x | M ≤ ‖x‖}`.
-/
theorem tight_from_conv_in_dist
    {X : ℕ → Ω → E} {Z : Ω → E}
    (hXZ : TendstoInDistribution X atTop Z μ)
    (M : ℝ) (hM : 0 < M) :
    ∀ η : ENNReal, 0 < η →
      ∃ N, ∀ n ≥ N,
        μ {ω | M ≤ ‖X n ω‖} ≤ μ.map Z {x | M ≤ ‖x‖} + η := by
  intro η hη;
  -- By the portmanteau theorem, we have that $\limsup_{n \to \infty} \mu(X_n \in F) \leq \mu(Z \in F)$ for any closed set $F$.
  have h_portmanteau : ∀ F : Set E, IsClosed F → Filter.limsup (fun n => μ {ω | X n ω ∈ F}) Filter.atTop ≤ (μ.map Z) F := by
    intro F hF;
    have := hXZ.tendsto;
    convert ProbabilityMeasure.limsup_measure_closed_le_of_tendsto this hF;
    erw [ MeasureTheory.Measure.map_apply_of_aemeasurable ];
    · rfl;
    · exact hXZ.forall_aemeasurable _;
    · exact hF.measurableSet;
  contrapose! h_portmanteau;
  refine' ⟨ { x | M ≤ ‖x‖ }, isClosed_le continuous_const continuous_norm, _ ⟩;
  refine' lt_of_lt_of_le _ ( le_limsup_of_frequently_le _ _ );
  exact ENNReal.lt_add_right ( show ( Measure.map Z μ ) { x | M ≤ ‖x‖ } ≠ ⊤ from MeasureTheory.measure_ne_top _ _ ) hη.ne';
  · exact Filter.frequently_atTop.2 fun N => by obtain ⟨ n, hn₁, hn₂ ⟩ := h_portmanteau N; exact ⟨ n, hn₁, le_of_lt hn₂ ⟩ ;
  · exact ⟨ μ Set.univ, Filter.eventually_atTop.2 ⟨ 0, fun n hn => MeasureTheory.measure_mono ( Set.subset_univ _ ) ⟩ ⟩

/-
The tail probability of the limiting measure can be made arbitrarily small.
-/
theorem tail_prob_small
    {Z : Ω → E} (hZ : AEMeasurable Z μ) :
    Filter.Tendsto (fun M => μ.map Z {x | M ≤ ‖x‖}) atTop (𝓝 0) := by
  convert MeasureTheory.tendsto_measure_iInter_atTop _ _ _;
  · rw [ show ( ⋂ n : ℝ, { x : E | n ≤ ‖x‖ } ) = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro x hx; exact absurd ( Set.mem_iInter.mp hx ( ‖x‖ + 1 ) ) ( by norm_num ) ] ; simp +decide;
  · infer_instance;
  · exact fun x => measurableSet_le measurable_const measurable_norm |> MeasurableSet.nullMeasurableSet;
  · exact fun x y hxy => Set.setOf_subset_setOf.2 fun z hz => le_trans hxy hz;
  · exact ⟨ 0, ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide [ hZ ] ) ) ⟩

/-
Set-theoretic inclusion underlying the splitting argument:
if `‖x − θ‖ < δ` and `‖sqrtN n • (x − θ)‖ < M` and the remainder bound
`‖r(x)‖ ≤ c ‖x − θ‖` holds with `c * M ≤ ε`, then `‖sqrtN n • r(x)‖ < ε`.
-/
theorem remainder_small_of_close
    {g : E → F} {J : E →L[ℝ] F} {θ x : E}
    {c ε M : ℝ} {n : ℕ}
    (hrem : ‖g x - g θ - J (x - θ)‖ ≤ c * ‖x - θ‖)
    (hc : 0 < c) (hM : ‖sqrtN n • (x - θ)‖ < M)
    (hcM : c * M ≤ ε) :
    ‖sqrtN n • (g x - g θ - J (x - θ))‖ < ε := by
  rw [ norm_smul, Real.norm_eq_abs, abs_of_nonneg ( Real.sqrt_nonneg _ ) ] at *;
  nlinarith [ Real.sqrt_nonneg n, norm_nonneg ( x - θ ) ]

/-! ### Scaled remainder convergence -/

/-
**Scaled remainder lemma.**
The scaled Taylor remainder `√n • (g(Tₙ) − g(θ) − J(Tₙ − θ))` converges to
zero in probability when `Tₙ →_p θ` and `√n (Tₙ − θ)` converges in
distribution.
-/
theorem scaled_remainder_tendstoInMeasure
    {T : ℕ → Ω → E} {θ : E} {Z : Ω → E}
    {g : E → F} {J : E →L[ℝ] F}
    (hderiv : HasFDerivAt g J θ)
    (hTprob : TendstoInMeasure μ (fun n ω ↦ T n ω - θ) atTop (fun _ ↦ 0))
    (hconv : TendstoInDistribution (fun n ω ↦ sqrtN n • (T n ω - θ)) atTop Z μ)
    (_hTmeas : ∀ n, AEMeasurable (T n) μ) :
    TendstoInMeasure μ
      (fun n ω ↦ sqrtN n • (g (T n ω) - g θ - J (T n ω - θ))) atTop (fun _ ↦ 0) := by
  -- By definition of TendstoInMeasure, we need to show that for every ε > 0, the measure of the set where the remainder exceeds ε tends to zero.
  rw [tendstoInMeasure_iff_norm] at *;
  intro ε hε
  have h_tail : ∀ η > 0, ∃ N, ∀ n ≥ N, μ {ω | ε ≤ ‖sqrtN n • (g (T n ω) - g θ - J (T n ω - θ))‖} ≤ η := by
    intro η hη
    obtain ⟨M₀, hM₀⟩ : ∃ M₀ > 0, μ.map Z {x | M₀ ≤ ‖x‖} < η / 4 := by
      have := tail_prob_small hconv.aemeasurable_limit;
      have := this.eventually ( gt_mem_nhds <| show 0 < η / 4 from ENNReal.div_pos_iff.mpr ⟨ hη.ne', by norm_num ⟩ ) ; have := this.and ( Filter.eventually_gt_atTop 0 ) ; obtain ⟨ M₀, hM₀₁, hM₀₂ ⟩ := this.exists; exact ⟨ M₀, hM₀₂, hM₀₁ ⟩ ;
    obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ n ≥ N₁, μ {ω | M₀ ≤ ‖sqrtN n • (T n ω - θ)‖} ≤ η / 2 := by
      have := tight_from_conv_in_dist hconv M₀ hM₀.1;
      obtain ⟨ N₁, hN₁ ⟩ := this ( η / 4 ) ( ENNReal.div_pos hη.ne' ( by norm_num ) );
      refine' ⟨ N₁, fun n hn => le_trans ( hN₁ n hn ) _ ⟩;
      convert add_le_add_right hM₀.2.le ( η / 4 ) using 1 ; ring;
      rw [ ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul ] ; ring;
      rw [ mul_assoc, mul_comm ];
      rw [ show ( 4 : ENNReal ) = 2 * 2 by norm_num, ENNReal.mul_inv ] ; ring;
      · simp +decide [ sq, mul_assoc ];
        rw [ ENNReal.inv_mul_cancel ] <;> norm_num;
      · norm_num;
      · exact Or.inl ENNReal.ofNat_ne_top;
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x, ‖x - θ‖ < δ → ‖g x - g θ - J (x - θ)‖ ≤ (ε / (2 * M₀)) * ‖x - θ‖ := by
      exact hasFDerivAt_remainder_bound hderiv ( ε / ( 2 * M₀ ) ) ( div_pos hε ( mul_pos zero_lt_two hM₀.1 ) );
    obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ n ≥ N₂, μ {ω | δ ≤ ‖T n ω - θ‖} ≤ η / 2 := by
      have := hTprob δ hδ_pos;
      simpa using this.eventually ( ge_mem_nhds <| ENNReal.half_pos hη.ne' );
    refine' ⟨ Max.max N₁ N₂, fun n hn => le_trans _ ( le_trans ( add_le_add ( hN₂ n ( le_trans ( le_max_right _ _ ) hn ) ) ( hN₁ n ( le_trans ( le_max_left _ _ ) hn ) ) ) _ ) ⟩;
    · refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      intro ω hω;
      contrapose! hω;
      simp_all +decide [ norm_smul ];
      refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( hδ _ hω.1 ) ( abs_nonneg _ ) ) _;
      nlinarith [ mul_div_cancel₀ ε ( by linarith : ( 2 * M₀ ) ≠ 0 ) ];
    · rw [ ENNReal.add_halves ];
  rw [ ENNReal.tendsto_nhds_zero ];
  aesop

/-! ### Main theorem -/

/-
**Multivariate Delta Method** (van der Vaart, *Asymptotic Statistics*,
Theorem 3.1).

If `√n (Tₙ − θ)` converges in distribution to `Z` and `g : E → F` is Fréchet
differentiable at `θ` with derivative `J`, then
`√n (g(Tₙ) − g(θ))` converges in distribution to `J ∘ Z`.

### Hypotheses

* `hconv` — `√n (Tₙ − θ) →_d Z`.
* `hderiv` — `g` is Fréchet differentiable at `θ` with derivative `J`.
* `hTprob` — `Tₙ →_p θ` (convergence in probability). This follows from
  `hconv` via tightness (Prokhorov) + scaling, but is stated explicitly to
  avoid dependence on Prokhorov's theorem.
* `hTmeas` — each `Tₙ` is AE-measurable.
* `hgmeas` — `g` is measurable (needed for push-forward measures).
-/
@[stat_lemma]
theorem multivariate_delta_method
    {T : ℕ → Ω → E} {θ : E} {Z : Ω → E}
    {g : E → F} {J : E →L[ℝ] F}
    (hconv : TendstoInDistribution (fun n ω ↦ sqrtN n • (T n ω - θ)) atTop Z μ)
    (hderiv : HasFDerivAt g J θ)
    (hTprob : TendstoInMeasure μ (fun n ω ↦ T n ω - θ) atTop (fun _ ↦ 0))
    (hTmeas : ∀ n, AEMeasurable (T n) μ)
    (hgmeas : Measurable g) :
    TendstoInDistribution (fun n ω ↦ sqrtN n • (g (T n ω) - g θ)) atTop
      (fun ω ↦ J (Z ω)) μ := by
  -- Apply the continuous mapping theorem to X and Z, using the fact that J is continuous.
  have hX_conv : TendstoInDistribution (fun n ω => J (sqrtN n • (T n ω - θ))) atTop (fun ω => J (Z ω)) μ := by
    exact hconv.continuous_comp J.continuous;
  convert tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX_conv _ _ using 1;
  · convert scaled_remainder_tendstoInMeasure hderiv hTprob hconv hTmeas using 1;
    ext; simp +decide [ smul_sub ];
  · exact fun n => AEMeasurable.const_smul ( hgmeas.comp_aemeasurable ( hTmeas n ) |> fun h => h.sub_const _ ) _

end Pythia.DeltaMethod