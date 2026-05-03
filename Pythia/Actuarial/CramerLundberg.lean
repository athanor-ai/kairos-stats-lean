/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cramér–Lundberg Classical Ruin Inequality

The foundational result of actuarial ruin theory. For a Cramér–Lundberg
surplus process with initial reserve u, Poisson claim arrivals at rate lam,
iid nonneg claim sizes X_i with premium rate c > lam * E[X] (net-profit
condition), and adjustment coefficient R > 0 satisfying

  E[exp(R * X)] = 1 + R * c / lam,

the ruin probability satisfies psi(u) <= exp(-R * u).

## Proof strategy

We work with the embedded discrete-time process at claim arrival epochs.
The cumulative claims at the n-th arrival are S_n = sum_{i<n} X_i,
and ruin occurs iff exists n, S_n > u + n * (c/lam).

Define the shifted exponential process
  M_n(w) = exp(R * (S_{n+1}(w) - (n+1) * c/lam))
which is adapted to the natural filtration F_n = sigma(X_0,...,X_n).

Key steps:
1. M is a non-negative supermartingale (uses independence + adjustment coeff).
2. E[M_0] <= 1 (from (1+x)*exp(-x) <= 1).
3. The ruin event is a subset of {exists n, M_n >= exp(R*u)}.
4. Ville's inequality gives P(exists n, M_n >= exp(R*u)) <= E[M_0]/exp(R*u) <= exp(-R*u).

## References

* Lundberg, F. (1903). Approximerad framstaellning av sannolikhetsfunktionen.
* Cramer, H. (1930). On the mathematical theory of risk.
* Asmussen, S. & Albrecher, H. (2010). Ruin Probabilities, Ch. III.5.
-/

import Mathlib
import Pythia.VilleSupermartingale

namespace Pythia.CramerLundberg

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Definitions -/

/-- Cumulative claims: the sum of the first `n` claim sizes. -/
def cumClaims (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, X i ω

/-- The ruin event: cumulative claims exceed the initial reserve `u`
    plus cumulative premiums `n * drift` at some claim arrival time `n`.
    Here `drift = c / lam` is the expected premium income per claim. -/
def ruinEvent (X : ℕ → Ω → ℝ) (drift u : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, cumClaims X n ω > u + ↑n * drift}

/-- The Cramér–Lundberg ruin probability psi(u). -/
def ruinProb (μ : Measure Ω) (X : ℕ → Ω → ℝ) (drift u : ℝ) : ℝ :=
  (μ (ruinEvent X drift u)).toReal

/-- The shifted exponential process M_n = exp(R * (S_{n+1} - (n+1)*drift)).
    This is adapted to the natural filtration sigma(X_0,...,X_n). -/
def expMG (X : ℕ → Ω → ℝ) (R drift : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  exp (R * (cumClaims X (n + 1) ω - ↑(n + 1) * drift))

/-! ### Analytical helper lemmas -/

/-- The inequality (1 + x) * exp(-x) <= 1 for all x : R. -/
lemma one_add_mul_exp_neg_le_one (x : ℝ) : (1 + x) * exp (-x) ≤ 1 := by
  nlinarith [Real.exp_pos (-x), Real.exp_neg x,
    mul_inv_cancel₀ (ne_of_gt (Real.exp_pos x)),
    Real.add_one_le_exp x, Real.add_one_le_exp (-x)]

/-- exp is nonneg -/
lemma expMG_nonneg (X : ℕ → Ω → ℝ) (R drift : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ expMG X R drift n ω :=
  exp_nonneg _

/-! ### MGF and moment bounds -/

/-
The MGF of each X_i at R equals 1 + R * drift (from IdentDistrib + hR_mgf).
-/
lemma mgf_X_eq [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {R drift : ℝ}
    (hR_mgf : ∫ ω, exp (R * X 0 ω) ∂μ = 1 + R * drift)
    (i : ℕ) :
    ∫ ω, exp (R * X i ω) ∂μ = 1 + R * drift := by
  rw [ ← hR_mgf ];
  have := h_dist i;
  exact this.comp ( measurable_id'.const_mul R |> Measurable.exp ) |> IdentDistrib.integral_eq

/-
The excess moment E[exp(R * (X_i - drift))] <= 1.
-/
lemma exp_excess_le_one [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int_exp : ∀ i, Integrable (fun ω => exp (R * X i ω)) μ)
    {R drift : ℝ}
    (hR_mgf : ∫ ω, exp (R * X 0 ω) ∂μ = 1 + R * drift)
    (i : ℕ) :
    ∫ ω, exp (R * (X i ω - drift)) ∂μ ≤ 1 := by
  -- Use the fact that $E[\exp(R * (X_i - drift))] = \exp(-R * drift) * E[\exp(R * X_i)]$.
  have h_exp : ∫ ω, Real.exp (R * (X i ω - drift)) ∂μ = Real.exp (-R * drift) * ∫ ω, Real.exp (R * X i ω) ∂μ := by
    rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; rw [ ← Real.exp_add ] ; ring;
  convert one_add_mul_exp_neg_le_one ( R * drift ) using 1 ; ring;
  convert h_exp using 1;
  · simp +decide only [mul_sub];
  · rw [ show ∫ ω, Real.exp ( R * X i ω ) ∂μ = 1 + R * drift by simpa using mgf_X_eq h_dist hR_mgf i ] ; ring

/-
E[M_0] = E[exp(R * (X_0 - drift))] <= 1.
-/
lemma expMG_initial_integral_le [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int_exp : ∀ i, Integrable (fun ω => exp (R * X i ω)) μ)
    {R drift : ℝ}
    (hR_mgf : ∫ ω, exp (R * X 0 ω) ∂μ = 1 + R * drift) :
    ∫ ω, expMG X R drift 0 ω ∂μ ≤ 1 := by
  -- By definition of `expMG`, we know that `expMG X R drift 0 ω = exp (R * (X 0 ω - drift))`.
  unfold expMG;
  convert exp_excess_le_one h_dist ( fun i => ?_ ) hR_mgf 0 using 1;
  rotate_left;
  exact 0;
  · norm_num;
  · unfold cumClaims; norm_num;

/-! ### Supermartingale property -/

/-
The factoring identity: M_{n+1} = M_n * exp(R*(X_{n+1} - drift)).
-/
lemma expMG_succ (X : ℕ → Ω → ℝ) (R drift : ℝ) (n : ℕ) (ω : Ω) :
    expMG X R drift (n + 1) ω =
      expMG X R drift n ω * exp (R * (X (n + 1) ω - drift)) := by
  unfold expMG;
  unfold cumClaims; push_cast [ Finset.sum_range_succ ] ; rw [ ← Real.exp_add ] ; ring;

/-
Each X_j for j ≤ n is strongly measurable wrt the natural filtration at n.
-/
lemma stronglyMeasurable_X_natural {X : ℕ → Ω → ℝ}
    (h_meas : ∀ i, Measurable (X i)) {j n : ℕ} (hjn : j ≤ n) :
    @StronglyMeasurable Ω ℝ _ ((Filtration.natural (β := fun _ : ℕ => ℝ)
      (fun i => X i) (fun i => (h_meas i).stronglyMeasurable)).seq n) (X j) := by
  refine' Measurable.stronglyMeasurable _;
  refine' Measurable.of_comap_le _;
  exact le_iSup_of_le j ( le_iSup_of_le hjn le_rfl )

/-
The exponential process is strongly adapted to the natural filtration.
-/
lemma expMG_stronglyAdapted {X : ℕ → Ω → ℝ}
    (h_meas : ∀ i, Measurable (X i)) (R drift : ℝ) :
    StronglyAdapted (Filtration.natural (β := fun _ : ℕ => ℝ)
      (fun i => X i) (fun i => (h_meas i).stronglyMeasurable))
      (fun i => (expMG X R drift i : Ω → ℝ)) := by
  intro n;
  have h_strong_meas : @StronglyMeasurable Ω ℝ _ ((Filtration.natural (β := fun _ : ℕ => ℝ)
    (fun i => X i) (fun i => (h_meas i).stronglyMeasurable)).seq n) (fun ω => cumClaims X (n + 1) ω) := by
      unfold cumClaims; simp +decide [ *, Finset.sum_range_succ ] ;
      -- The sum of strongly measurable functions is strongly measurable.
      have h_sum_strong_meas : ∀ (s : Finset ℕ), (∀ i ∈ s, @StronglyMeasurable Ω ℝ _ ((Filtration.natural (β := fun _ : ℕ => ℝ)
          (fun i => X i) (fun i => (h_meas i).stronglyMeasurable)).seq n) (X i)) → @StronglyMeasurable Ω ℝ _ ((Filtration.natural (β := fun _ : ℕ => ℝ)
          (fun i => X i) (fun i => (h_meas i).stronglyMeasurable)).seq n) (fun ω => ∑ i ∈ s, X i ω) := by
            exact?;
      exact h_sum_strong_meas ( Finset.range n ) ( fun i hi => stronglyMeasurable_X_natural ( fun i => h_meas i ) ( Finset.mem_range_le hi ) ) |> fun h => h.add ( stronglyMeasurable_X_natural ( fun i => h_meas i ) le_rfl );
  apply_rules [ Real.continuous_exp.comp_stronglyMeasurable, h_strong_meas ];
  exact StronglyMeasurable.const_mul ( h_strong_meas.sub ( stronglyMeasurable_const ) ) _

/-- Each expMG term is integrable. -/
lemma expMG_integrable [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    {R drift : ℝ}
    (h_int_exp : ∀ i, Integrable (fun ω => exp (R * X i ω)) μ)
    (n : ℕ) :
    Integrable (expMG X R drift n) μ := by
  show Integrable (fun ω => exp (R * (cumClaims X (n + 1) ω - ↑(n + 1) * drift))) μ
  have h1 : (fun ω => exp (R * (∑ i ∈ range (n + 1), X i ω - ↑(n + 1) * drift))) =
      (fun ω => exp (R * ∑ i ∈ range (n + 1), X i ω) * exp (-(R * (↑(n + 1) * drift)))) := by
    ext ω; rw [← exp_add]; ring_nf
  simp only [cumClaims]
  rw [h1]
  have h2 : Integrable (fun ω => exp (R * ∑ i ∈ range (n + 1), X i ω)) μ := by
    have := h_iid.integrable_exp_mul_sum (t := R) (s := range (n+1))
      h_meas (fun i _ => h_int_exp i)
    convert this using 1; ext ω; simp [Finset.sum_apply]
  exact h2.mul_const _

/-
The one-step conditional expectation bound:
    E[M_{n+1} | F_n] ≤ M_n.
-/
lemma expMG_condexp_le [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {R drift : ℝ}
    (h_int_exp : ∀ i, Integrable (fun ω => exp (R * X i ω)) μ)
    (hR_pos : 0 < R)
    (hdrift_pos : 0 < drift)
    (hR_mgf : ∫ ω, exp (R * X 0 ω) ∂μ = 1 + R * drift)
    (n : ℕ) :
    let 𝒢 := Filtration.natural (β := fun _ : ℕ => ℝ) (fun i => X i)
          (fun i => (h_meas i).stronglyMeasurable)
    μ[expMG X R drift (n + 1) | 𝒢 n] ≤ᵐ[μ] expMG X R drift n := by
  have h_step : let 𝒢 := Filtration.natural (fun i => X i) (fun i => (h_meas i).stronglyMeasurable);
    μ[fun ω => Real.exp (R * (X (n + 1) ω - drift)) | 𝒢 n] ≤ᶠ[ae μ] 1 := by
      have h_step : let 𝒢 := Filtration.natural (fun i => X i) (fun i => (h_meas i).stronglyMeasurable);
        μ[fun ω => Real.exp (R * (X (n + 1) ω - drift)) | 𝒢 n] =ᵐ[μ] fun ω => ∫ ω, Real.exp (R * (X (n + 1) ω - drift)) ∂μ := by
          have h_expMG_le_one : let 𝒢 := (Filtration.natural (fun i => X i) (fun i => (h_meas i).stronglyMeasurable));
              Indep (MeasurableSpace.comap (fun ω => X (n + 1) ω) inferInstance) (𝒢 n) μ := by
                apply_rules [ iIndepFun.indep_comap_natural_of_lt ];
                exact Nat.lt_succ_self n;
          have h_expMG_le_one : let 𝒢 := (Filtration.natural (fun i => X i) (fun i => (h_meas i).stronglyMeasurable));
              @StronglyMeasurable Ω ℝ _ (MeasurableSpace.comap (fun ω => X (n + 1) ω) inferInstance) (fun ω => Real.exp (R * (X (n + 1) ω - drift))) := by
                apply_rules [ Measurable.stronglyMeasurable, Measurable.exp, Measurable.mul, Measurable.sub, measurable_const ];
                grind +suggestions;
          grind +suggestions;
      have h_step : ∫ ω, Real.exp (R * (X (n + 1) ω - drift)) ∂μ ≤ 1 := by
        apply_rules [ exp_excess_le_one ];
      filter_upwards [ ‹let 𝒢 := Filtration.natural ( fun i => X i ) ( fun i => ( h_meas i ).stronglyMeasurable ) ; μ[fun ω => Real.exp ( R * ( X ( n + 1 ) ω - drift ) ) | 𝒢 n] =ᶠ[ae μ] fun ω => ∫ ω, Real.exp ( R * ( X ( n + 1 ) ω - drift ) ) ∂μ› ] with ω hω using hω.symm ▸ h_step;
  have h_mul : let 𝒢 := Filtration.natural (fun i => X i) (fun i => (h_meas i).stronglyMeasurable);
    μ[fun ω => expMG X R drift n ω * Real.exp (R * (X (n + 1) ω - drift)) | 𝒢 n] ≤ᶠ[ae μ] expMG X R drift n * 1 := by
      have h_mul : let 𝒢 := Filtration.natural (fun i => X i) (fun i => (h_meas i).stronglyMeasurable);
        μ[fun ω => expMG X R drift n ω * Real.exp (R * (X (n + 1) ω - drift)) | 𝒢 n] =ᶠ[ae μ] expMG X R drift n * μ[fun ω => Real.exp (R * (X (n + 1) ω - drift)) | 𝒢 n] := by
          apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
          · exact expMG_stronglyAdapted h_meas R drift n;
          · have h_integrable : ∀ i, Integrable (fun ω => Real.exp (R * X i ω)) μ := by
              intro i
              have h_integrable : Integrable (fun ω => Real.exp (R * X 0 ω)) μ := by
                exact ( by contrapose! hR_mgf; rw [ MeasureTheory.integral_undef hR_mgf ] ; positivity );
              have := h_dist i;
              exact this.comp ( measurable_id'.const_mul R |> Measurable.exp ) |> fun h => h.integrable_iff.mpr h_integrable;
            convert expMG_integrable h_iid h_meas h_integrable ( n + 1 ) using 1;
            exact funext fun ω => by rw [ Pi.mul_apply, expMG_succ ] ;
          · have h_integrable : ∀ i, Integrable (fun ω => Real.exp (R * X i ω)) μ := by
              intro i
              have h_integrable : Integrable (fun ω => Real.exp (R * X 0 ω)) μ := by
                exact ( by contrapose! hR_mgf; rw [ MeasureTheory.integral_undef hR_mgf ] ; positivity );
              have := h_dist i;
              exact this.comp ( measurable_id'.const_mul R |> Measurable.exp ) |> fun h => h.integrable_iff.mpr h_integrable;
            convert h_integrable ( n + 1 ) |> fun h => h.mul_const ( Real.exp ( -R * drift ) ) using 2 ; rw [ ← Real.exp_add ] ; ring;
      filter_upwards [ h_mul, h_step ] with ω hω₁ hω₂ using by simpa only [ hω₁ ] using mul_le_mul_of_nonneg_left hω₂ ( expMG_nonneg X R drift n ω ) ;
  convert h_mul using 1;
  simp +decide [ ← expMG_succ ]

/-- The exponential process M is a non-negative supermartingale
    with respect to the natural filtration of X. -/
theorem expMG_supermartingale [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {R drift : ℝ}
    (h_int_exp : ∀ i, Integrable (fun ω => exp (R * X i ω)) μ)
    (hR_pos : 0 < R)
    (hdrift_pos : 0 < drift)
    (hR_mgf : ∫ ω, exp (R * X 0 ω) ∂μ = 1 + R * drift) :
    let 𝒢 := Filtration.natural (β := fun _ : ℕ => ℝ) (fun i => X i)
          (fun i => (h_meas i).stronglyMeasurable)
    Supermartingale (expMG X R drift) 𝒢 μ := by
  intro 𝒢
  apply supermartingale_nat (expMG_stronglyAdapted h_meas R drift)
  · intro i; exact expMG_integrable h_iid h_meas h_int_exp i
  · intro i
    exact expMG_condexp_le h_iid h_meas h_dist h_int_exp hR_pos hdrift_pos hR_mgf i

/-! ### Ruin event containment -/

/-- The ruin event is contained in {w | exists n, M_n(w) >= exp(R*u)}.
    This holds because ruin at time m >= 1 means S_m > u + m*drift,
    hence M_{m-1} = exp(R*(S_m - m*drift)) > exp(R*u). -/
lemma ruinEvent_subset (X : ℕ → Ω → ℝ) (R drift u : ℝ) (hR : 0 < R) (hu : 0 ≤ u) :
    ruinEvent X drift u ⊆
      {ω | ∃ n : ℕ, expMG X R drift n ω ≥ exp (R * u)} := by
  intro ω hω
  obtain ⟨n, hn⟩ := hω
  by_cases hn0 : n = 0
  · simp_all +decide [cumClaims]; linarith
  · use n - 1
    rcases n <;> simp_all +decide [cumClaims, expMG]
    linarith

/-! ### Main theorem -/

/-
**Cramér–Lundberg Ruin Inequality.**
    For iid nonneg claims with adjustment coefficient R > 0 satisfying
    E[exp(R*X)] = 1 + R*(c/lam), the ruin probability is at most exp(-R*u).
-/
theorem cramer_lundberg_ruin
    [IsProbabilityMeasure μ]
    (u : ℝ) (hu : 0 ≤ u)
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (hlam : 0 < lam)
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (_h_pos : ∀ i ω, 0 ≤ X i ω)
    (_h_int : Integrable (X 0) μ)
    (_h_safety : c > lam * (∫ ω, X 0 ω ∂μ))
    (R : ℝ) (hR_pos : 0 < R)
    (hR_def : ∫ ω, exp (R * X 0 ω) ∂μ = 1 + R * c / lam)
    (h_int_exp : ∀ i, Integrable (fun ω => exp (R * X i ω)) μ) :
    let ψ : ℝ → ℝ := fun u => ruinProb μ X (c / lam) u
    ψ u ≤ exp (-R * u) := by
  refine' le_trans ( ENNReal.toReal_mono _ _ ) _;
  exact ( ∫ ω, expMG X R ( c / lam ) 0 ω ∂μ ).toNNReal / ( Real.exp ( R * u ) |> ENNReal.ofReal );
  · exact ENNReal.div_ne_top ( by norm_num ) ( by positivity );
  · have h_supermartingale : Supermartingale (expMG X R (c / lam)) (Filtration.natural (β := fun _ : ℕ => ℝ) (fun i => X i) (fun i => (h_meas i).stronglyMeasurable)) μ := by
      apply expMG_supermartingale h_iid h_meas h_dist h_int_exp hR_pos (by
      positivity) (by
      rw [ hR_def, mul_div ]);
    have h_ville : μ {ω | ∃ n, expMG X R (c / lam) n ω ≥ Real.exp (R * u)} ≤ (∫ ω, expMG X R (c / lam) 0 ω ∂μ).toNNReal / (Real.exp (R * u)).toNNReal := by
      convert Pythia.ville_supermartingale h_supermartingale _ _ _ using 1;
      · exact fun t ω => Real.exp_nonneg _;
      · unfold expMG;
        convert h_int_exp 0 |> fun h => h.mul_const ( Real.exp ( -R * ( c / lam ) ) ) using 2 ; norm_num [ cumClaims ] ; ring;
        rw [ ← Real.exp_add, sub_eq_add_neg ];
      · positivity;
    refine' le_trans _ ( h_ville.trans _ );
    · exact MeasureTheory.measure_mono ( ruinEvent_subset X R ( c / lam ) u hR_pos hu );
    · rw [ ENNReal.ofReal ];
  · rw [ ENNReal.toReal_div, ENNReal.toReal_ofReal ( Real.exp_nonneg _ ) ];
    simp +zetaDelta at *;
    rw [ max_eq_left ( MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ), Real.exp_neg ];
    exact mul_le_of_le_one_left ( by positivity ) ( expMG_initial_integral_le h_dist h_int_exp ( by simpa [ mul_div_assoc ] using hR_def ) )

end

end Pythia.CramerLundberg