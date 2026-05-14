/-
Pythia.VilleSupermartingale — Ville's inequality for non-negative supermartingales.

**Theorem:** For a non-negative supermartingale `M` on filtration `𝓕` with
`M_0` integrable, and any `c > 0`:
    `μ{ω : ∃ t, M_t(ω) ≥ c} ≤ E[M_0] / c`
-/

import Mathlib
import Pythia.Basic

namespace Pythia

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}

/-! ### Helper: Optional stopping for supermartingales -/

/-
For a supermartingale `f`, the expected stopped value at a bounded stopping
time `τ` is at most `E[f 0]`. Derived by negation from the submartingale
version `Submartingale.expected_stoppedValue_mono`.
-/
theorem supermartingale_expected_stoppedValue_le
    (hsup : Supermartingale f 𝓕 μ)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝓕 τ) {N : ℕ} (hτN : ∀ ω, τ ω ≤ ↑N) :
    ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, f 0 ω ∂μ := by
  -- Apply the submartingale version of the optional stopping theorem to -f with stopping times τ₁ = fun _ => (0 : ℕ∞) and τ₂ = τ.
  have h_sub : ∫ ω, stoppedValue (-f) (fun _ => 0) ω ∂μ ≤ ∫ ω, stoppedValue (-f) τ ω ∂μ := by
    apply_rules [ Submartingale.expected_stoppedValue_mono ];
    · exact Supermartingale.neg hsup;
    · exact isStoppingTime_const 𝓕 0;
    · exact fun _ => zero_le _;
  simp_all +decide [ MeasureTheory.integral_neg, stoppedValue ]

/-! ### Helper: Markov-type bound for the stopped process -/

/-
On the event `{ω | ∃ t ∈ Finset.range (N+1), c ≤ f t ω}`, the stopped
value at the hitting time of `{y | c ≤ y}` in `[0,N]` is at least `c`.
-/
theorem stoppedValue_ge_of_hitting
    (_hnonneg : ∀ t ω, 0 ≤ f t ω)
    {c : ℝ} (_hc : 0 < c) (N : ℕ) (ω : Ω)
    (hω : ∃ t, t ∈ Finset.range (N + 1) ∧ c ≤ f t ω) :
    c ≤ stoppedValue f (fun ω' => ↑(hittingBtwn f {y | c ≤ y} 0 N ω')) ω := by
  apply hittingBtwn_mem_set; aesop;

/-! ### Helper: Monotone union for the existential event -/

/-
The event `{ω | ∃ t, c ≤ f t ω}` is the union over `N` of
`{ω | ∃ t ∈ Finset.range (N+1), c ≤ f t ω}`.
-/
theorem exists_ge_eq_iUnion_range
    {c : ℝ} :
    {ω : Ω | ∃ t : ℕ, f t ω ≥ c} = ⋃ N : ℕ, {ω | ∃ t, t ∈ Finset.range (N + 1) ∧ c ≤ f t ω} := by
  ext ω; aesop;

/-
The sets `{ω | ∃ t ∈ range(N+1), c ≤ f t ω}` are monotone in `N`.
-/
theorem monotone_exists_range
    {c : ℝ} :
    Monotone (fun N => {ω : Ω | ∃ t, t ∈ Finset.range (N + 1) ∧ c ≤ f t ω}) := by
  exact fun N M hNM ω hω => by obtain ⟨ t, ht₁, ht₂ ⟩ := hω; exact ⟨ t, Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp ht₁ ] ), ht₂ ⟩ ;

/-! ### Helper: Finite-horizon bound -/

/-
For each `N`, `μ{ω | ∃ t ≤ N, c ≤ f t ω} ≤ E[f 0] / c` using
optional stopping + Markov.
-/
theorem ville_finite_horizon
    (hsup : Supermartingale f 𝓕 μ) (hnonneg : ∀ t ω, 0 ≤ f t ω)
    (_hint : Integrable (f 0) μ)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    μ {ω : Ω | ∃ t, t ∈ Finset.range (N + 1) ∧ c ≤ f t ω} ≤
      (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  -- Let g = stoppedValue f τ_N
  set g : Ω → ℝ := fun ω => stoppedValue f (fun ω' => ↑(hittingBtwn f {y | c ≤ y} 0 N ω')) ω;
  have h_integrable : MeasureTheory.Integrable g μ := by
    have : ∀ {τ : Ω → ℕ∞}, IsStoppingTime 𝓕 τ → (∀ ω, τ ω ≤ N) → MeasureTheory.Integrable (stoppedValue f τ) μ := by
      have := hsup.integrable;
      exact fun {τ} a a_1 => integrable_stoppedValue ℕ a this a_1
    apply this;
    · apply_rules [ Adapted.isStoppingTime_hittingBtwn ];
      · grind +suggestions;
      · exact measurableSet_Ici;
    · simp +zetaDelta at *;
      exact fun ω => hittingBtwn_le ω;
  have h_markov : c * μ.real {ω | g ω ≥ c} ≤ ∫ ω, g ω ∂μ := by
    apply_rules [ mul_meas_ge_le_integral_of_nonneg ];
    filter_upwards [ ] with ω using hnonneg _ _;
  have h_subset : {ω | ∃ t ∈ Finset.range (N + 1), c ≤ f t ω} ⊆ {ω | g ω ≥ c} := by
    exact fun ω hω => stoppedValue_ge_of_hitting hnonneg hc N ω hω;
  have h_final : c * μ.real {ω | ∃ t ∈ Finset.range (N + 1), c ≤ f t ω} ≤ ∫ ω, f 0 ω ∂μ := by
    refine' le_trans ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_subset ) hc.le ) ( h_markov.trans _ );
    · exact MeasureTheory.measure_ne_top _ _;
    · apply_rules [ supermartingale_expected_stoppedValue_le ];
      · apply_rules [ Adapted.isStoppingTime_hittingBtwn ];
        · grind +suggestions;
        · exact measurableSet_Ici;
      · simp +decide [ hittingBtwn_le ];
  rw [ ENNReal.le_div_iff_mul_le ] <;> norm_cast;
  · rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · simp_all +decide [ Finset.mem_range ];
      exact Or.inl ( by rwa [ max_eq_left hc.le, mul_comm ] );
    · exact ENNReal.mul_ne_top ( MeasureTheory.measure_ne_top _ _ ) ( ENNReal.coe_ne_top );
  · exact Or.inl ( ne_of_gt ( Real.toNNReal_pos.mpr hc ) );
  · exact Or.inl ENNReal.coe_ne_top

/-! ### Main theorem -/

/-
**Ville's inequality for non-negative supermartingales.**

For a non-negative supermartingale `f` on filtration `𝓕` with finite measure
space, and any threshold `c > 0`, the probability that the supermartingale
ever exceeds `c` is bounded by `E[f_0] / c`.
-/
theorem ville_supermartingale
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : @Filtration Ω ℕ _ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnonneg : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  convert ( ville_finite_horizon hsup hnonneg ‹_› hc ) using 1;
  rw [ exists_ge_eq_iUnion_range ];
  constructor <;> intro h;
  · exact fun N => ville_finite_horizon hsup hnonneg hint hc N;
  · convert le_of_tendsto_of_tendsto' ( MeasureTheory.tendsto_measure_iUnion_atTop ( monotone_exists_range ) ) tendsto_const_nhds h using 1

/-! ### Corollary: unit-initial case -/

/-
**Corollary: Ville's inequality for a unit-initial-value supermartingale.**

When `f 0 = 1` almost surely, the bound reduces to `1/c`.
-/
theorem ville_supermartingale_unit_initial
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : @Filtration Ω ℕ _ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnonneg : ∀ t ω, 0 ≤ f t ω)
    (hunit : ∀ᵐ ω ∂μ, f 0 ω = 1)
    {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (1 / c).toNNReal := by
  convert ville_supermartingale hsup hnonneg _ hc using 1;
  · rw [ MeasureTheory.integral_congr_ae hunit, MeasureTheory.integral_const ] ; norm_num;
    norm_num [ ← ENNReal.ofReal_coe_nnreal ];
    rw [ ENNReal.ofReal_inv_of_pos hc ];
  · exact hsup.integrable 0

/-- **Constant `c > 0` preserves positivity.** -/
theorem ville_bound_pos {c : ℝ} (hc : 0 < c) : 0 < (1 / c).toNNReal := by
  rw [Real.toNNReal_pos]
  exact div_pos one_pos hc

end Pythia