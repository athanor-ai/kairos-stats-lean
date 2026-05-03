/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.AEPBernoulli

Asymptotic Equipartition Property (AEP) for iid Bernoulli(p) samples:
for X₁, X₂, … iid Bernoulli(p), the normalized log-likelihood
    (1/n) ∑ log P(Xᵢ) →ᵃˢ −H(p)
where H(p) = Real.binEntropy p is the binary Shannon entropy.

This is Cover–Thomas, *Elements of Information Theory*, Theorem 3.1.2.

**Proof strategy.**  Define `bernoulliLogLik p : Bool → ℝ` by
`true ↦ log p`, `false ↦ log(1−p)`.  The compositions
`bernoulliLogLik p ∘ Xᵢ` are iid real-valued random variables; the
Strong Law of Large Numbers (`ProbabilityTheory.strong_law_ae`)
gives almost-sure convergence of their Cesàro means to
`𝔼[bernoulliLogLik p ∘ X₀] = p log p + (1−p) log(1−p) = −H(p)`.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset Real
open scoped ENNReal NNReal

namespace Pythia.InformationTheory

/-- Log-likelihood of a single Bernoulli(p) observation. -/
noncomputable def bernoulliLogLik (p : ℝ) : Bool → ℝ :=
  fun b => if b then Real.log p else Real.log (1 - p)

/-! ### Helper lemmas -/

/-- Any function `Bool → ℝ` is measurable (Bool is discrete). -/
lemma bernoulliLogLik_measurable (p : ℝ) : Measurable (bernoulliLogLik p) :=
  measurable_of_finite _

/-- Composition `bernoulliLogLik p ∘ X 0` is integrable on a probability space
    (a bounded function composed with a measurable map). -/
lemma bernoulliLogLik_comp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : Ω → Bool) (hX : Measurable X) (p : ℝ) :
    Integrable (bernoulliLogLik p ∘ X) μ :=
  Integrable.comp_measurable Integrable.of_finite hX

/-
Pairwise independence transfers through measurable maps.
-/
lemma bernoulliLogLik_pairwise_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → Bool) (p : ℝ)
    (h_indep : Pairwise (Function.onFun (fun f g => IndepFun f g μ) X)) :
    Pairwise (Function.onFun (fun f g => IndepFun f g μ)
      (fun i => bernoulliLogLik p ∘ X i)) := by
  intro i j hij
  exact (h_indep hij).comp (bernoulliLogLik_measurable p) (bernoulliLogLik_measurable p)

/-
Identical distribution transfers through measurable maps.
-/
lemma bernoulliLogLik_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → Bool) (p : ℝ)
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ i, IdentDistrib (bernoulliLogLik p ∘ X i) (bernoulliLogLik p ∘ X 0) μ μ := by
  intro i; have := h_ident i; exact this.comp (bernoulliLogLik_measurable p)

/-
The integral of `bernoulliLogLik p ∘ X₀` equals `−binEntropy p`.
-/
lemma bernoulliLogLik_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → Bool) (hX : Measurable X) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hprob : μ (X ⁻¹' {true}) = ENNReal.ofReal p) :
    ∫ ω, bernoulliLogLik p (X ω) ∂μ = -(binEntropy p) := by
  -- Use integral_map (hX.aemeasurable) to rewrite as integral over Bool with pushforward measure.
  have h_integral_map : ∫ ω, (bernoulliLogLik p (X ω)) ∂μ = ∫ b, (bernoulliLogLik p b) ∂(MeasureTheory.Measure.map X μ) := by
    rw [ MeasureTheory.integral_map ];
    · exact hX.aemeasurable;
    · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( MeasurableSet.singleton _ ) measurable_const measurable_const );
  rw [ h_integral_map, MeasureTheory.integral_fintype ];
  · simp +decide [*, bernoulliLogLik, binEntropy];
    rw [ MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, Measure.map_apply ] <;> norm_num [ hX, hprob ];
    rw [ show X ⁻¹' { false } = ( X ⁻¹' { true } ) ᶜ by ext; aesop, MeasureTheory.measure_compl ] <;> norm_num [ hprob, hp0.le, hp1.le ];
    · module;
    · exact hX ( MeasurableSingletonClass.measurableSet_singleton _ );
  · norm_num +zetaDelta at *

/-
**Asymptotic Equipartition Property for iid Bernoulli(p).**
(Cover–Thomas, Theorem 3.1.2.)

For `X₀, X₁, …` iid `Bernoulli(p)` on a probability space `(Ω, μ)`,
```
  (1/n) ∑_{i<n} log P(Xᵢ)  →ᵃˢ  −H(p)
```
where `H(p) = binEntropy p` is the binary Shannon entropy.
-/
theorem aep_bernoulli
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : Pairwise (Function.onFun (fun f g => IndepFun f g μ) X))
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_prob : μ (X 0 ⁻¹' {true}) = ENNReal.ofReal p) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun (n : ℕ) => (n : ℝ)⁻¹ • ∑ i ∈ range n, bernoulliLogLik p (X i ω))
      atTop
      (nhds (-(binEntropy p))) := by
  -- Define Y : ℕ → Ω → ℝ := fun i => bernoulliLogLik p ∘ X i.
  set Y : ℕ → Ω → ℝ := fun i ω => bernoulliLogLik p (X i ω);
  -- Apply the strong law of large numbers to the sequence $Y_i$.
  have h_strong_law : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / (n : ℝ)) Filter.atTop (nhds (∫ ω, Y 0 ω ∂μ)) := by
    have := @ProbabilityTheory.strong_law_ae;
    specialize this Y (bernoulliLogLik_comp_integrable (X 0) (hX_meas 0) p) (bernoulliLogLik_pairwise_indep X p hX_indep) (bernoulliLogLik_identDistrib X p hX_ident);
    simpa [ div_eq_inv_mul ] using this;
  convert h_strong_law using 4 ; norm_num [ div_eq_inv_mul ];
  · exact Or.inl rfl;
  · exact Eq.symm ( bernoulliLogLik_integral _ ( hX_meas 0 ) _ hp0 hp1 hX_prob )

end Pythia.InformationTheory