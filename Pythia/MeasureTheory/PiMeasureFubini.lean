/-
Helper lemmas for pi measure Fubini factorization.
-/
import Mathlib

open scoped ENNReal NNReal MeasureTheory
open MeasureTheory MeasureTheory.Measure Filter ProbabilityTheory Finset

noncomputable section

/-! ## Pi measure Fubini factorization -/

/-
**Fubini factorization for pi measures (probability case).**
The integral of a product of independent functions over a pi measure
equals the product of the individual integrals.
-/
theorem lintegral_pi_finset_prod_prob
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ ω, Finset.univ.prod (fun i => f i (ω i)) ∂(Measure.pi ν) =
    Finset.univ.prod (fun i => ∫⁻ x, f i x ∂(ν i)) := by
  have := @lintegral_prod_eq_prod_lintegral_of_indepFun
  specialize @this ((i : ι) → Ω i) _ (Measure.pi ν) ι Finset.univ
    (fun i ω => f i (ω i))
  simp_all +decide [iIndepFun]
  convert this _ _
  · rename_i i _
    rw [← MeasureTheory.lintegral_map']
    · rw [MeasureTheory.Measure.map_id']
      have h_map : MeasureTheory.Measure.map
          (fun ω : (i : ι) → Ω i => ω i) (Measure.pi ν) = ν i := by
        ext s hs
        rw [Measure.map_apply]
        · rw [show (fun ω : (i : ι) → Ω i => ω i) ⁻¹' s =
              (Set.pi Set.univ fun j => if h : j = i then h ▸ s else Set.univ) from ?_]
          · rw [MeasureTheory.Measure.pi_pi]
            rw [Finset.prod_eq_single i] <;> aesop
          · grind
        · exact measurable_pi_apply i
        · exact hs
      rw [← h_map, MeasureTheory.lintegral_map]
      · exact hf i
      · exact measurable_pi_apply i
    · exact (hf i |> Measurable.aemeasurable)
    · exact aemeasurable_id
  · convert iIndepFun_pi _
    · assumption
    · exact fun i => (hf i).aemeasurable
  · exact fun i => hf i |> Measurable.comp <| measurable_pi_apply i

/-
Absolute continuity of finite product measures (probability case).
-/
theorem finProd_absolutelyContinuous_prob
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ ν : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hac : ∀ i, (μ i) ≪ (ν i)) :
    Measure.pi μ ≪ Measure.pi ν := by
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs hνs
  have h_prod_zero : ∫⁻ ω in s, (∏ i, (μ i).rnDeriv (ν i) (ω i)) ∂(Measure.pi ν) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hνs, MeasureTheory.lintegral_zero_measure]
  convert h_prod_zero using 1
  rw [← MeasureTheory.withDensity_apply _ hs, MeasureTheory.Measure.pi_eq]
  intro s hs
  rw [MeasureTheory.withDensity_apply']
  rw [← MeasureTheory.lintegral_indicator]
  · convert lintegral_pi_finset_prod_prob ν
      (fun i => (s i).indicator (fun x => (μ i |> MeasureTheory.Measure.rnDeriv) (ν i) x))
      (fun i => Measurable.indicator (by measurability) (hs i)) using 1
    · congr with ω; by_cases hω : ∀ i, ω i ∈ s i <;> simp +decide [hω]
      rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.choose (not_forall.mp hω)))
        (by simp +decide [Classical.choose_spec (not_forall.mp hω)])]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [MeasureTheory.lintegral_indicator]
      · rw [MeasureTheory.Measure.setLIntegral_rnDeriv]; aesop
      · exact hs i
  · exact MeasurableSet.univ_pi hs

/-
Fubini factorization for Fin n (sigma-finite, full integral).
-/
theorem lintegral_fin_prod_sigmaFinite :
    ∀ (n : ℕ) (Ω : Fin n → Type*) [inst : ∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [inst2 : ∀ i, SigmaFinite (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (_ : ∀ i, Measurable (f i)),
    ∫⁻ ω, Finset.univ.prod (fun i => f i (ω i)) ∂(Measure.pi ν) =
    Finset.univ.prod (fun i => ∫⁻ x, f i x ∂(ν i)) := by
  intro n
  induction' n with n ih <;> simp_all +decide [Fin.prod_univ_succ]
  intro Ω _ ν _ f hf
  have h_measure_preserving : MeasurePreserving (MeasurableEquiv.piFinSuccAbove Ω 0) (Measure.pi ν)
      ((ν 0).prod (Measure.pi (fun j => ν (Fin.succAbove 0 j)))) := by
    exact?
  convert h_measure_preserving.lintegral_comp
    (show Measurable fun p : Ω 0 × ((i : Fin n) → Ω (Fin.succAbove 0 i)) =>
      f 0 p.1 * ∏ i, f (Fin.succ i) (p.2 i) from ?_) using 1
  · have h_lintegral_prod :
      ∀ (μ : Measure (Ω 0)) [SigmaFinite μ]
        (ν : Measure ((i : Fin n) → Ω (Fin.succAbove 0 i))) [SigmaFinite ν]
        (f : Ω 0 → ℝ≥0∞) (g : ((i : Fin n) → Ω (Fin.succAbove 0 i)) → ℝ≥0∞),
        Measurable f → Measurable g →
        ∫⁻ (b : Ω 0 × ((i : Fin n) → Ω (Fin.succAbove 0 i))), f b.1 * g b.2 ∂(μ.prod ν) =
        (∫⁻ (x : Ω 0), f x ∂μ) * ∫⁻ (y : ((i : Fin n) → Ω (Fin.succAbove 0 i))), g y ∂ν := by
      intros μ _ ν _ f g hf hg
      convert MeasureTheory.lintegral_prod_mul hf.aemeasurable hg.aemeasurable using 1
      infer_instance
    convert h_lintegral_prod (ν 0) (Measure.pi fun j => ν (Fin.succAbove 0 j)) (f 0)
      (fun ω => ∏ i, f (Fin.succ i) (ω i)) (hf 0)
      (Finset.measurable_prod _ fun i _ => hf (Fin.succ i) |> Measurable.comp <|
        measurable_pi_apply i) |> Eq.symm using 1
    simp +decide [Fin.succAbove]
    rw [ih]
    exact fun i => hf _
  · fun_prop

/-- **Fubini factorization for pi measures (sigma-finite case, full integral).** -/
theorem lintegral_pi_finset_prod_sigmaFinite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ ω, Finset.univ.prod (fun i => f i (ω i)) ∂(Measure.pi ν) =
    Finset.univ.prod (fun i => ∫⁻ x, f i x ∂(ν i)) := by
  obtain ⟨e⟩ := Fintype.truncEquivFin ι
  have mp := measurePreserving_piCongrLeft ν e.symm
  have step1 : ∫⁻ ω, univ.prod (fun i => f i (ω i)) ∂(Measure.pi ν) =
      ∫⁻ ω, univ.prod (fun i => f i ((MeasurableEquiv.piCongrLeft Ω e.symm) ω i))
        ∂(Measure.pi (fun i' => ν (e.symm i'))) :=
    (mp.lintegral_comp (Finset.measurable_prod _ fun i _ =>
      (hf i).comp (measurable_pi_apply i))).symm
  rw [step1]; clear step1
  have step2 : ∀ ω : (∀ j : Fin (Fintype.card ι), Ω (e.symm j)),
      univ.prod (fun i : ι => f i ((MeasurableEquiv.piCongrLeft Ω e.symm) ω i)) =
      univ.prod (fun j : Fin (Fintype.card ι) => f (e.symm j) (ω j)) := by
    intro ω; rw [← e.symm.prod_comp]; congr 1; ext j
    congr 1; exact MeasurableEquiv.piCongrLeft_apply_apply e.symm ω j
  simp_rw [step2]
  rw [lintegral_fin_prod_sigmaFinite _ (fun j => Ω (e.symm j))
    (fun j => ν (e.symm j)) (fun j => f (e.symm j)) (fun j => hf _),
    ← e.symm.prod_comp]

/-- **Fubini factorization for pi measures (sigma-finite case, set integral).**
The set integral of a product of functions depending on single coordinates
factors into a product of set integrals. -/
theorem setLIntegral_pi_finset_prod_sigmaFinite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (s : ∀ i, Set (Ω i)) (hs : ∀ i, MeasurableSet (s i)) :
    ∫⁻ ω in Set.univ.pi s, Finset.univ.prod (fun i => f i (ω i)) ∂(Measure.pi ν) =
    Finset.univ.prod (fun i => ∫⁻ x in s i, f i x ∂(ν i)) := by
  have h_indicator : ∫⁻ ω in Set.univ.pi s, ∏ i, f i (ω i) ∂Measure.pi ν =
      ∫⁻ ω, (∏ i, (s i).indicator (f i) (ω i)) ∂Measure.pi ν := by
    rw [← MeasureTheory.lintegral_indicator]
    · congr with ω
      by_cases h : ∀ i, ω i ∈ s i <;> simp +decide [h, Set.indicator_apply]
      rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.choose (not_forall.mp h)))
        (Set.indicator_of_notMem (Classical.choose_spec (not_forall.mp h)) _)]
    · exact MeasurableSet.univ_pi hs
  rw [h_indicator, lintegral_pi_finset_prod_sigmaFinite]
  · exact Finset.prod_congr rfl fun i _ => by rw [MeasureTheory.lintegral_indicator (hs i)]
  · exact fun i => Measurable.indicator (hf i) (hs i)

/-
The withDensity of a pi measure with a product density equals the
pi measure of the withDensity measures.
-/
theorem pi_withDensity_prod_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hfint : ∀ i, ∫⁻ x, f i x ∂(ν i) < ⊤) :
    (Measure.pi ν).withDensity (fun ω => Finset.univ.prod (fun i => f i (ω i))) =
    Measure.pi (fun i => (ν i).withDensity (f i)) := by
  have h_prod_density : ∀ (s : ∀ i, Set (Ω i)), (∀ i, MeasurableSet (s i)) →
      (Measure.pi ν).withDensity (fun ω => ∏ i, f i (ω i)) (Set.pi Set.univ s) =
      ∏ i, (ν i).withDensity (f i) (s i) := by
    intro s hs
    rw [MeasureTheory.withDensity_apply']
    have h_prod_density : ∫⁻ ω in Set.pi Set.univ s, ∏ i, f i (ω i) ∂Measure.pi ν =
        ∫⁻ ω, ∏ i, (s i).indicator (f i) (ω i) ∂Measure.pi ν := by
      rw [← MeasureTheory.lintegral_indicator]
      · congr with ω; by_cases hω : ∀ i, ω i ∈ s i <;>
          simp +decide [hω, Set.indicator_apply]
        rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.choose (not_forall.mp hω)))
          (by simp +decide [Classical.choose_spec (not_forall.mp hω)])]
      · exact MeasurableSet.univ_pi hs
    convert lintegral_pi_finset_prod_prob ν (fun i => (s i).indicator (f i))
      (fun i => ?_) using 1
    · simp +decide [MeasureTheory.withDensity_apply, hs]
    · exact Measurable.indicator (hf i) (hs i)
  rw [MeasureTheory.Measure.pi_eq]
  convert rfl
  convert MeasureTheory.Measure.pi_eq _
  any_goals exact MeasureTheory.Measure.pi ν
  · intro i
    use fun n => Set.univ
    · exact fun _ => Set.mem_univ _
    · simp +decide [MeasureTheory.withDensity_apply, hfint]
    · aesop
  · exact h_prod_density
  · exact?

end
