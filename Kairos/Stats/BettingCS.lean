/-
Kairos.Stats.BettingCS — formalised betting CS construction
(Waudby-Smith and Ramdas 2024).

The betting confidence sequence stops when the log-wealth of a
bounded adaptive betting strategy first exceeds the log inverse of
the stated coverage level: `log W_t ≥ log(1 / alpha)`.  Admissibility
follows from Ville's inequality applied to the wealth supermartingale.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.StoppingRule
import Kairos.Stats.BettingStrategy
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

/-- Betting stopping rule: fire when the log-wealth first exceeds
`log(1 / alpha)`, and stay fired forever after (a true stopping rule).
The decision at time `t` is `true` iff there exists some `s ≤ t` with
`m s ≥ log(1 / alpha)`. -/
noncomputable def bettingStoppingRule
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (alpha : ℝ) : StoppingRule 𝓕 where
  decide m t := decide (∃ s, s ≤ t ∧ m s ≥ Real.log (1 / alpha))
  monotone_once_fired := by
    intro m t ht
    simp only [decide_eq_true_eq] at ht ⊢
    obtain ⟨s, hle, hge⟩ := ht
    exact ⟨s, by omega, hge⟩

/-- The event `∃ t, decide m t = true` under the existential
definition is equivalent to the simpler `∃ t, m t ≥ log(1/alpha)`. -/
private lemma bettingStoppingRule_exists_iff
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (alpha : ℝ) (m : ℕ → ℝ) :
    (∃ t, (bettingStoppingRule σ ξ alpha).decide m t = true) ↔
    (∃ t, m t ≥ Real.log (1 / alpha)) := by
  simp only [bettingStoppingRule, decide_eq_true_eq]
  constructor
  · rintro ⟨t, s, _, hs⟩; exact ⟨s, hs⟩
  · rintro ⟨t, ht⟩; exact ⟨t, t, le_refl _, ht⟩

/-
Ville's inequality for non-negative supermartingales, infinite horizon:
    `μ{∃ t, c ≤ Y t ω} ≤ E[Y 0] / c`.
    Follows from the finite-horizon `ville_supermartingale` by taking the
    supremum over N, using continuity of measure from below.
-/
lemma ville_supermartingale_infinite
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Y : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hY : Supermartingale Y 𝓕 μ) (hY_nn : ∀ t ω, 0 ≤ Y t ω)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, c ≤ Y t ω} ≤
      ENNReal.ofReal ((∫ ω, Y 0 ω ∂μ) / c) := by
  by_contra h_contra;
  have h_lim : Filter.Tendsto (fun N => μ {ω | ∃ t ≤ N, c ≤ Y t ω}) Filter.atTop (nhds (μ {ω | ∃ t, c ≤ Y t ω})) := by
    convert MeasureTheory.tendsto_measure_iUnion_atTop _;
    · ext ω; simp [Set.mem_iUnion];
      exact ⟨ fun ⟨ t, ht ⟩ => ⟨ t, t, le_rfl, ht ⟩, fun ⟨ i, t, ht, ht' ⟩ => ⟨ t, ht' ⟩ ⟩;
    · infer_instance;
    · exact fun n m hnm ω hω => by obtain ⟨ t, ht, ht' ⟩ := hω; exact ⟨ t, le_trans ht hnm, ht' ⟩ ;
  exact h_contra <| le_of_tendsto_of_tendsto' h_lim tendsto_const_nhds fun N => ville_supermartingale hY hY_nn hc N

/-
The betting stopping rule event is contained in the wealth-threshold event.
-/
lemma betting_event_subset_wealth
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound : ∀ t ω, |σ.lam t ω * ξ t ω| < 1)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    {ω | ∃ t, (bettingStoppingRule σ ξ alpha).decide
                 (fun t => logWealthProcess σ ξ t ω) t = true} ⊆
    {ω | ∃ t, (1 / alpha) ≤ wealthProcess σ ξ t ω} := by
  intro ω;
  simp +decide only [bettingStoppingRule_exists_iff, Set.mem_setOf_eq];
  rintro ⟨ t, ht ⟩;
  contrapose! ht;
  refine' Real.log_lt_log _ ( ht t );
  induction' t with t ih;
  · exact zero_lt_one;
  · exact mul_pos ih ( by nlinarith [ abs_lt.mp ( h_bound t ω ) ] )

/-
Integral of the wealth process at time 0 equals 1.
-/
lemma wealthProcess_integral_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ) :
    ∫ ω, wealthProcess σ ξ 0 ω ∂μ = 1 := by
  simp [wealthProcess]

/-
Admissibility of the betting rule.
-/
theorem bettingStoppingRule_admissible
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound : ∀ t ω, |σ.lam t ω * ξ t ω| < 1)
    (h_xi_adapted : Adapted 𝓕 ξ)
    (h_integrable : ∀ t, Integrable (ξ t) μ)
    (h_wealth_integrable : ∀ t, Integrable (wealthProcess σ ξ t) μ)
    (h_zero_mean : ∀ t, μ[(ξ t) | 𝓕 t] =ᵐ[μ] 0)
    (h_martingale : Martingale (wealthProcess σ ξ) 𝓕 μ)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    μ {ω | ∃ t, (bettingStoppingRule σ ξ alpha).decide
                 (fun t => logWealthProcess σ ξ t ω) t = true} ≤
      ENNReal.ofReal alpha := by
  have h_admissible : μ {ω | ∃ t, (1 / alpha) ≤ wealthProcess σ ξ t ω} ≤ ENNReal.ofReal alpha := by
    have h_admissible : μ {ω | ∃ t, (1 / alpha) ≤ wealthProcess σ ξ t ω} ≤ ENNReal.ofReal ((∫ ω, wealthProcess σ ξ 0 ω ∂μ) / (1 / alpha)) := by
      have := @ville_supermartingale_infinite;
      exact this ( h_martingale.supermartingale ) ( fun t ω => wealthProcess_nonneg σ ξ h_bound t ω ) ( one_div_pos.mpr halpha.1 );
    convert h_admissible using 2 ; norm_num [ wealthProcess_integral_zero ];
  refine' le_trans ( MeasureTheory.measure_mono _ ) h_admissible;
  exact betting_event_subset_wealth σ ξ h_bound alpha halpha

end Kairos.Stats