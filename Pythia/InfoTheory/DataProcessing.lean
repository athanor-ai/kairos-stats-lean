/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/
import Mathlib

/-!
# Data Processing Inequality for KL Divergence

The **Data Processing Inequality** (DPI) states that processing data through a Markov kernel
cannot increase the KL divergence between two measures. Formally, for a Markov kernel
`κ : Kernel Ω Ω'` and finite measures `μ, ν` on `Ω` with `ν ≪ μ`:

  `klDiv (ν.bind κ) (μ.bind κ) ≤ klDiv ν μ`

This is a fundamental result in information theory (Cover–Thomas, *Elements of Information
Theory*, Chapter 2).

## Proof strategy

We decompose the proof into three steps via the composition–product measures `μ ⊗ₘ κ`
and `ν ⊗ₘ κ` on the product space `Ω × Ω'`:

1. **`rnDeriv_compProd_right`**: `∂(ν ⊗ₘ κ)/∂(μ ⊗ₘ κ) (x, y) = ∂ν/∂μ x` a.e.,
   since the kernel component is the same.
2. **`klDiv_compProd_right`**: `klDiv (ν ⊗ₘ κ) (μ ⊗ₘ κ) = klDiv ν μ`,
   using step 1 and the Fubini-type `lintegral_compProd`.
3. **`klDiv_fst_le`**: `klDiv P.fst Q.fst ≤ klDiv P Q` for joint measures `P ≪ Q`,
   using the conditional kernel (disintegration `Q = Q.fst ⊗ₘ Q.condKernel`) and
   Jensen's inequality for the convex function `klFun`.
4. **`klDiv_snd_le`**: obtained from `klDiv_fst_le` via `Prod.swap`.

The main theorem follows: by `snd_compProd`, `(μ ⊗ₘ κ).snd = μ.bind κ`, so
  `klDiv (ν.bind κ) (μ.bind κ) = klDiv (ν ⊗ₘ κ).snd (μ ⊗ₘ κ).snd
    ≤ klDiv (ν ⊗ₘ κ) (μ ⊗ₘ κ) = klDiv ν μ`.

## Main results

* `Pythia.InfoTheory.AbsolutelyContinuous.bind_right`: `ν ≪ μ → ν.bind κ ≪ μ.bind κ`.
* `Pythia.InfoTheory.klDiv_bind_le_klDiv`: the Data Processing Inequality.

## References

* Cover, Thomas. *Elements of Information Theory*. Wiley, 1991. Chapter 2.
-/

open MeasureTheory ProbabilityTheory InformationTheory Measure

open scoped ENNReal

namespace Pythia.InfoTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ### Absolute continuity under kernel composition -/

/-
If `ν ≪ μ` then `ν.bind κ ≪ μ.bind κ` for any measurable kernel `κ`.
-/
theorem AbsolutelyContinuous.bind_right {μ ν : Measure Ω}
    (hνμ : ν ≪ μ) (κ : Kernel Ω Ω') :
    ν.bind κ ≪ μ.bind κ := by
  refine' MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs => _;
  rw [ MeasureTheory.Measure.bind_apply hs, MeasureTheory.Measure.bind_apply hs ];
  · rw [ MeasureTheory.lintegral_eq_zero_iff ];
    · exact fun h => MeasureTheory.lintegral_congr_ae ( hνμ h ) |> Eq.trans <| MeasureTheory.lintegral_zero;
    · exact?;
  · exact?;
  · exact?

/-! ### Radon–Nikodym derivative of compProd with same kernel -/

/-
When ν ≪ μ and we form product measures with the same kernel κ,
the Radon–Nikodym derivative `∂(ν ⊗ₘ κ)/∂(μ ⊗ₘ κ)` at `(x, y)` equals `∂ν/∂μ x` a.e.
-/
theorem rnDeriv_compProd_right {μ ν : Measure Ω} {κ : Kernel Ω Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    (hνμ : ν ≪ μ) :
    (fun p : Ω × Ω' => ν.rnDeriv μ p.1) =ᵐ[μ ⊗ₘ κ] (ν ⊗ₘ κ).rnDeriv (μ ⊗ₘ κ) := by
  symm;
  have h_eq : (μ ⊗ₘ κ).withDensity (fun p => ν.rnDeriv μ p.1) = ν ⊗ₘ κ := by
    ext s hs;
    -- By Fubini's theorem, we can interchange the order of integration.
    have h_fubini : ∫⁻ (a : Ω × Ω') in s, (ν.rnDeriv μ a.1) ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b in s.preimage (Prod.mk a), (ν.rnDeriv μ a) ∂(κ a) ∂μ := by
      rw [ ← MeasureTheory.lintegral_indicator ];
      · rw [ MeasureTheory.Measure.lintegral_compProd ];
        · congr! 2;
          rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
          · rfl;
          · exact measurable_prodMk_left hs;
        · exact Measurable.indicator ( by exact Measurable.comp ( MeasureTheory.Measure.measurable_rnDeriv _ _ ) measurable_fst ) hs;
      · exact hs;
    simp_all +decide [ MeasureTheory.Measure.compProd_apply, MeasureTheory.Measure.restrict_apply ];
    have h_fubini : ∫⁻ (a : Ω), (κ a) (Prod.mk a ⁻¹' s) ∂ν = ∫⁻ (a : Ω), (κ a) (Prod.mk a ⁻¹' s) * (ν.rnDeriv μ a) ∂μ := by
      have h_fubini : ∀ f : Ω → ENNReal, Measurable f → ∫⁻ (a : Ω), f a ∂ν = ∫⁻ (a : Ω), f a * (ν.rnDeriv μ a) ∂μ := by
        intro f hf;
        have := @MeasureTheory.lintegral_rnDeriv_mul;
        convert this hνμ ( hf.aemeasurable ) |> Eq.symm using 1;
        ac_rfl;
      apply h_fubini;
      exact?;
    simp_all +decide [ mul_comm ];
  convert MeasureTheory.Measure.rnDeriv_withDensity _ _;
  · exact h_eq.symm;
  · infer_instance;
  · exact Measurable.comp ( MeasureTheory.Measure.measurable_rnDeriv _ _ ) measurable_fst

/-
KL divergence is invariant under taking compProd with the same Markov kernel.
-/
theorem klDiv_compProd_right {μ ν : Measure Ω} {κ : Kernel Ω Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    (hνμ : ν ≪ μ) :
    klDiv (ν ⊗ₘ κ) (μ ⊗ₘ κ) = klDiv ν μ := by
  by_cases hνμ' : ν ≪ μ;
  · rw [ klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun ];
    -- By definition of compProd, we have that the Radon-Nikodym derivative of ν ⊗ₘ κ with respect to μ ⊗ₘ κ is the same as the Radon-Nikodym derivative of ν with respect to μ.
    have h_rnDeriv : (ν ⊗ₘ κ).rnDeriv (μ ⊗ₘ κ) =ᵐ[μ ⊗ₘ κ] fun p => ν.rnDeriv μ p.1 := by
      exact?;
    rw [ if_pos, if_pos hνμ' ];
    · rw [ MeasureTheory.lintegral_congr_ae ( h_rnDeriv.mono fun x hx => by rw [ hx ] ) ];
      erw [ MeasureTheory.Measure.lintegral_compProd ];
      · simp +decide [ klFun ];
      · fun_prop;
    · exact?;
  · contradiction

/-! ### KL divergence of marginals -/

/-
KL divergence is preserved under measurable equivalences.
-/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    klDiv (P.map e) (Q.map e) = klDiv P Q := by
  by_cases hPQ : P ≪ Q <;> simp_all +decide [ InformationTheory.klDiv_eq_lintegral_klFun ];
  · rw [ if_pos ( by exact MeasureTheory.Measure.AbsolutelyContinuous.map hPQ e.measurable ) ];
    rw [ MeasureTheory.lintegral_map' ];
    · have h_rnDeriv_map : ∀ᵐ x ∂Q, (P.map e).rnDeriv (Q.map e) (e x) = P.rnDeriv Q x := by
        have := @MeasurableEmbedding.rnDeriv_map;
        exact this e.measurableEmbedding P Q;
      exact MeasureTheory.lintegral_congr_ae ( by filter_upwards [ h_rnDeriv_map ] with x hx; rw [ hx ] );
    · fun_prop;
    · exact e.measurable.aemeasurable;
  · intro h;
    contrapose! hPQ;
    refine' MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs => _;
    intro hsQ
    have h_eq : P s = (P.map e) (e '' s) := by
      rw [ MeasureTheory.Measure.map_apply ];
      · rw [ Set.preimage_image_eq _ e.injective ];
      · exact e.measurable;
      · exact e.measurableSet_image.mpr hs;
    rw [ h_eq, h ];
    rw [ MeasureTheory.Measure.map_apply e.measurable ];
    · rwa [ e.preimage_image ];
    · exact e.measurableSet_image.mpr hs

/-
The rnDeriv of the first marginal equals the conditional integral of the joint rnDeriv
with respect to the conditional kernel.
-/
theorem rnDeriv_fst_eq_lintegral_condKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β]
    {P Q : Measure (α × β)} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) :
    (fun x => (P.fst.rnDeriv Q.fst x : ℝ≥0∞)) =ᵐ[Q.fst]
      fun x => ∫⁻ y, P.rnDeriv Q (x, y) ∂Q.condKernel x := by
  have h_cond : Q = Q.fst ⊗ₘ Q.condKernel := by
    exact?;
  have h_abs_cont : P.fst ≪ Q.fst := by
    refine' MeasureTheory.Measure.AbsolutelyContinuous.mk _;
    intro s hs hQ_zero
    have hP_zero : P (s ×ˢ Set.univ) = 0 := by
      refine' hPQ _;
      convert h_cond.symm ▸ MeasureTheory.Measure.compProd_apply ( hs.prod MeasurableSet.univ );
      rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero ];
      filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hQ_zero ] with x hx using by simp +decide [ hx ] ;
    rw [ MeasureTheory.Measure.fst_apply hs ];
    convert hP_zero using 2 ; ext ; simp +decide;
  refine' MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite _ _ _;
  · exact?;
  · fun_prop;
  · intro s hs hQs
    have h_eq : ∫⁻ x in s, (∂P.fst/∂Q.fst) x ∂Q.fst = P.fst s := by
      exact?;
    have h_eq : ∫⁻ x in s, (∫⁻ y, (∂P/∂Q) (x, y) ∂Q.condKernel x) ∂Q.fst = ∫⁻ p in s ×ˢ Set.univ, (∂P/∂Q) p ∂Q := by
      have h_eq : ∫⁻ x in s, (∫⁻ y, (∂P/∂Q) (x, y) ∂Q.condKernel x) ∂Q.fst = ∫⁻ p in s ×ˢ Set.univ, (∂P/∂Q) p ∂(Q.fst ⊗ₘ Q.condKernel) := by
        rw [ ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ];
        · erw [ MeasureTheory.Measure.lintegral_compProd ];
          · congr with x ; by_cases hx : x ∈ s <;> simp +decide [ hx ];
          · exact Measurable.indicator ( MeasureTheory.Measure.measurable_rnDeriv _ _ ) ( hs.prod MeasurableSet.univ );
        · exact hs.prod MeasurableSet.univ;
        · exact hs;
      rw [ h_eq, ← h_cond ];
    have h_eq : ∫⁻ p in s ×ˢ Set.univ, (∂P/∂Q) p ∂Q = P (s ×ˢ Set.univ) := by
      exact?;
    rw [ ‹∫⁻ x in s, ( ∂P.fst/∂Q.fst ) x ∂Q.fst = P.fst s›, ‹∫⁻ x in s, ∫⁻ y, ( ∂P/∂Q ) ( x, y ) ∂Q.condKernel x ∂Q.fst = ∫⁻ p in s ×ˢ Set.univ, ( ∂P/∂Q ) p ∂Q›, h_eq ];
    rw [ MeasureTheory.Measure.fst_apply hs ];
    exact congr_arg _ ( by ext; simp +decide )

/-
Jensen's inequality for `klFun` applied to conditional integrals:
if `μ` is a probability measure and `∫⁻ f dμ < ∞`, then
`ofReal (klFun (∫⁻ f dμ).toReal) ≤ ∫⁻ ofReal (klFun (f x).toReal) dμ`.

The proof uses `mul_klFun_le_toReal_klDiv` (Jensen for the KL f-divergence)
applied to the withDensity measure `μ.withDensity f`.
-/
theorem lintegral_klFun_le_of_prob
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ≥0∞} (hf : Measurable f) (hf_fin : ∫⁻ x, f x ∂μ ≠ ⊤) :
    ENNReal.ofReal (klFun (∫⁻ x, f x ∂μ).toReal) ≤
      ∫⁻ x, ENNReal.ofReal (klFun (f x).toReal) ∂μ := by
  -- Let's set `ν := μ.withDensity f` and note that `ν` is a finite measure.
  set ν : Measure α := μ.withDensity f
  have hν_finite : IsFiniteMeasure ν := by
    exact?;
  -- By definition of `klDiv`, we have `klDiv ν μ = ∫⁻ x, ofReal (klFun (f x).toReal) ∂μ`.
  have h_klDiv : klDiv ν μ = ∫⁻ x, ENNReal.ofReal (klFun (f x).toReal) ∂μ := by
    rw [ klDiv_eq_lintegral_klFun ];
    rw [ if_pos ( MeasureTheory.withDensity_absolutelyContinuous _ _ ) ];
    exact MeasureTheory.lintegral_congr_ae ( by filter_upwards [ MeasureTheory.Measure.rnDeriv_withDensity μ hf ] with x hx; aesop );
  by_cases h : klDiv ν μ = ⊤;
  · exact h_klDiv ▸ h.symm ▸ le_top;
  · have := mul_klFun_le_toReal_klDiv ( show ν ≪ μ from ?_ ) ?_ <;> simp_all +decide [ MeasureTheory.measureReal_def ];
    · rw [ ENNReal.ofReal_le_iff_le_toReal ] <;> aesop;
    · exact?;
    · contrapose! h;
      rw [ ← h_klDiv, klDiv ];
      grobner

/-
The KL divergence of first marginals is at most the KL divergence of the joint measures.
Requires `StandardBorelSpace` on the second component for the disintegration theorem.
-/
theorem klDiv_fst_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β]
    {P Q : Measure (α × β)} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) :
    klDiv P.fst Q.fst ≤ klDiv P Q := by
  rw [klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun];
  split_ifs;
  · -- By Fubini's theorem, we can interchange the order of integration.
    have h_fubini : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (klFun ((P.rnDeriv Q (x, y)).toReal)) ∂Q.condKernel x ∂Q.fst = ∫⁻ z, ENNReal.ofReal (klFun ((P.rnDeriv Q z).toReal)) ∂Q := by
      have h_fubini : ∫⁻ z, ENNReal.ofReal (klFun ((P.rnDeriv Q z).toReal)) ∂Q = ∫⁻ z, ENNReal.ofReal (klFun ((P.rnDeriv Q z).toReal)) ∂(Q.fst ⊗ₘ Q.condKernel) := by
        rw [ MeasureTheory.Measure.disintegrate ];
      rw [ h_fubini, lintegral_compProd ];
      fun_prop;
    rw [ ← h_fubini ];
    refine' MeasureTheory.lintegral_mono_ae _;
    filter_upwards [rnDeriv_fst_eq_lintegral_condKernel hPQ,
                     Measure.rnDeriv_lt_top P.fst Q.fst] with x hx hx_fin;
    rw [hx]
    have h_fin : ∫⁻ y, (∂P/∂Q) (x, y) ∂Q.condKernel x ≠ ⊤ := by
      rw [← hx]; exact hx_fin.ne
    exact lintegral_klFun_le_of_prob
      (measurable_rnDeriv _ _ |>.comp (measurable_const.prodMk measurable_id)) h_fin;
  · contrapose! hPQ;
    intro h;
    refine' ‹¬P.fst ≪ Q.fst› ( MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs hs' => _ );
    rw [ MeasureTheory.Measure.fst_apply hs ] at *;
    exact h hs'

/-
The KL divergence of second marginals is at most the KL divergence of the
joint measures. Uses `klDiv_fst_le` via `Prod.swap`.
-/
theorem klDiv_snd_le [StandardBorelSpace Ω] [Nonempty Ω]
    {P Q : Measure (Ω × Ω')} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) :
    klDiv P.snd Q.snd ≤ klDiv P Q := by
  have hswap_le : klDiv (P.map Prod.swap).fst (Q.map Prod.swap).fst ≤ klDiv (P.map Prod.swap) (Q.map Prod.swap) := by
    apply_rules [ klDiv_fst_le ];
    apply_rules [ MeasureTheory.Measure.AbsolutelyContinuous.map, hPQ ];
    fun_prop;
  have hswap_eq : klDiv (P.map Prod.swap) (Q.map Prod.swap) = klDiv P Q := by
    apply klDiv_map_measurableEquiv (MeasurableEquiv.prodComm) P Q;
  aesop

/-! ### Data Processing Inequality -/

/-
**Data Processing Inequality for KL divergence.**
For a Markov kernel `κ` and finite measures `μ, ν` on `Ω` with `ν ≪ μ`,
the KL divergence cannot increase under kernel composition:
`klDiv (ν.bind κ) (μ.bind κ) ≤ klDiv ν μ`.

The `StandardBorelSpace Ω` hypothesis is used for the measure disintegration
(conditional kernel) that underpins the Jensen-inequality step.
The result holds in full generality (for arbitrary measurable spaces) but the
proof in that setting requires a variational characterisation of KL divergence
that is not yet available in Mathlib.
-/
theorem klDiv_bind_le_klDiv (κ : Kernel Ω Ω') [IsMarkovKernel κ]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hνμ : ν ≪ μ) :
    klDiv (ν.bind κ) (μ.bind κ) ≤ klDiv ν μ := by
  rw [ ← MeasureTheory.Measure.snd_compProd, ← MeasureTheory.Measure.snd_compProd ];
  convert klDiv_snd_le _;
  rw [ klDiv_compProd_right hνμ ];
  · infer_instance;
  · grind;
  · infer_instance;
  · constructor ; aesop;
  · exact?

end Pythia.InfoTheory