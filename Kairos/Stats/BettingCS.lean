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
`log(1 / alpha)`.  The log-wealth is tracked via `logWealthProcess`
of a given `BettingStrategy`. -/
noncomputable def bettingStoppingRule
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (alpha : ℝ) : StoppingRule 𝓕 where
  decide m t := decide (m t ≥ Real.log (1 / alpha))
  monotone_once_fired := by
    sorry

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
  -- Taking the limit as $N$ approaches infinity, we get the desired inequality.
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
  intro ω hω
  obtain ⟨t, ht⟩ := hω
  use t
  simp [logWealthProcess] at ht ⊢
  exact (by
  have h_wealth_nonneg : 0 ≤ wealthProcess σ ξ t ω := by
    exact wealthProcess_nonneg σ ξ h_bound t ω;
  have h_wealth_pos : 0 < wealthProcess σ ξ t ω := by
    contrapose! ht;
    simp +decide [ bettingStoppingRule, show wealthProcess σ ξ t ω = 0 by linarith ];
    exact Real.log_neg halpha.1 halpha.2;
  have h_wealth_pos : Real.log (wealthProcess σ ξ t ω) ≥ Real.log (1 / alpha) := by
    unfold bettingStoppingRule at ht; aesop;
  rw [ ge_iff_le, Real.log_le_log_iff ] at h_wealth_pos <;> aesop)

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
Admissibility of the betting rule: for every wealth-process
martingale (bounded strategy against a zero-conditional-mean centred
increment), the induced stopping rule has stopping probability at
most `alpha`.  Proof via Ville's inequality applied to the wealth
supermartingale at threshold `1 / alpha`.

Note: we assume the martingale property as a hypothesis since
`wealthProcess_martingale` is currently sorry'd (being proved
in a separate job).
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
  convert ville_supermartingale_infinite ( h_martingale.supermartingale ) ( fun t ω => ?_ ) ?_ using 1;
  any_goals exact one_div_pos.mpr halpha.1;
  · congr! 1;
    convert betting_event_subset_wealth σ ξ h_bound alpha halpha |> Set.Subset.antisymm <| ?_ using 1;
    intro ω hω
    obtain ⟨t, ht⟩ := hω
    use t
    simp [bettingStoppingRule];
    rw [ ← Real.log_inv ];
    exact Real.log_le_log ( inv_pos.mpr halpha.1 ) ( by simpa using ht );
  · rw [ wealthProcess_integral_zero, one_div_one_div ];
  · exact wealthProcess_nonneg σ ξ h_bound t ω

end Kairos.Stats