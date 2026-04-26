/-
Pythia.PhiTransform — the exponential betting-transform from a
self-normalized CS to a betting-form wealth process.
-/

import Mathlib
import Pythia.Basic
import Pythia.SubGaussianMG
import Pythia.HowardRamdasCS

namespace Pythia

open MeasureTheory ProbabilityTheory

/-! ## The betting-transform -/

/-- Optimised tilt `λ*(α, T)`. -/
noncomputable def phiTilt (sigma : ℝ) (alpha : ℝ) (T : ℕ) : ℝ :=
  if T = 0 then 0 else
    Real.sqrt (2 * Real.log ((T : ℝ) * (T + 1) / alpha) / (sigma^2 * T))

/-- The Φ-transform applied to an HR-family sub-Gaussian martingale. -/
noncomputable def phiProcess
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} (M : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω =>
    let lam := phiTilt sigma alpha T
    Real.exp (lam * M t ω - lam^2 * sigma^2 * t / 2)

/-! ## Helper lemmas -/

/-
`phiTilt` is non-negative (it's a `Real.sqrt`).
-/
lemma phiTilt_nonneg (sigma alpha : ℝ) (T : ℕ) : 0 ≤ phiTilt sigma alpha T := by
  unfold phiTilt;
  positivity

/-
`phiProcess` equals the ratio form used by `exp_process_is_supermartingale`.
-/
lemma phiProcess_eq_ratio (sigma alpha : ℝ) (T : ℕ) {Ω : Type*} (M : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    phiProcess sigma alpha T M t ω =
      Real.exp (phiTilt sigma alpha T * M t ω) /
        Real.exp (phiTilt sigma alpha T ^ 2 * sigma ^ 2 * t / 2) := by
  unfold phiProcess;
  rw [ ← Real.exp_sub ]

/-
At t=0, `phiProcess` equals `exp(lam * M 0 ω)`. Using `hM0`, this is 1 a.s.
-/
lemma phiProcess_zero_ae_eq_one
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (M : ℕ → Ω → ℝ)
    (hM0 : M 0 =ᵐ[μ] 0) :
    (fun ω => phiProcess sigma alpha T M 0 ω) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  filter_upwards [ hM0 ] with ω hω using by simp +decide [ hω, phiProcess ] ;

/-
The integral of `phiProcess` at time 0 equals 1.
-/
lemma integral_phiProcess_zero_eq_one
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (hM0 : M 0 =ᵐ[μ] 0) :
    ∫ ω, phiProcess sigma alpha T M 0 ω ∂μ = 1 := by
  convert MeasureTheory.integral_const ( 1 : ℝ ) using 1;
  rw [ MeasureTheory.integral_congr_ae ];
  · exact phiProcess_zero_ae_eq_one sigma alpha T M hM0;
  · simp +decide [ MeasureTheory.measureReal_def ]

/-
`phiProcess` is a supermartingale.
-/
lemma phiProcess_supermartingale
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG sigma 𝓕 μ) :
    Supermartingale (phiProcess sigma alpha T M.process) 𝓕 μ := by
  convert exp_process_is_supermartingale M ( phiTilt sigma alpha T ) ( phiTilt_nonneg sigma alpha T ) using 1;
  exact funext fun t => funext fun ω => phiProcess_eq_ratio sigma alpha T M.process t ω

/-
`phiProcess` is non-negative.
-/
lemma phiProcess_nonneg (sigma alpha : ℝ) (T : ℕ) {Ω : Type*} (M : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ phiProcess sigma alpha T M t ω := by
  exact Real.exp_nonneg _

/-! ## Target theorem -/

theorem phi_transform_hr_admissible
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1)
    (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG sigma 𝓕 μ)
    (hM0 : M.process 0 =ᵐ[μ] 0) :
    μ {ω | ∃ t ≤ 2^b,
            phiProcess sigma alpha (2^b) M.process t ω
              ≥ 1 / alpha}
      ≤ ENNReal.ofReal alpha := by
  -- Step 1: Rewrite ≥ to ≤ form matching ville_supermartingale
  have h_set_eq : {ω | ∃ t ≤ 2^b, phiProcess sigma alpha (2^b) M.process t ω ≥ 1 / alpha}
      = {ω | ∃ t : ℕ, t ≤ 2^b ∧ 1 / alpha ≤ phiProcess sigma alpha (2^b) M.process t ω} := by
    ext ω; simp only [ge_iff_le, Set.mem_setOf_eq]
  rw [h_set_eq]
  -- Step 2: Apply ville_supermartingale
  have h_sm := phiProcess_supermartingale sigma hσ alpha (2^b) M
  have h_nn : ∀ t ω, 0 ≤ phiProcess sigma alpha (2^b) M.process t ω :=
    phiProcess_nonneg sigma alpha (2^b) M.process
  have h_c_pos : (0 : ℝ) < 1 / alpha := div_pos one_pos halpha.1
  have h_ville := ville_supermartingale_finite h_sm h_nn h_c_pos (2^b)
  refine le_trans h_ville ?_
  -- Step 3: Simplify ∫ Y 0 / (1/alpha) = 1 / (1/alpha) = alpha
  rw [integral_phiProcess_zero_eq_one sigma alpha (2^b) M.process hM0]
  have halpha_pos := halpha.1
  have : 1 / (1 / alpha) = alpha := by field_simp
  rw [this]

/-! ## Vector-case Phi-transform (Aristotle target A) -/

/-- Vector-family optimised tilt: same algebraic shape as `phiTilt`
but scaled for `c_vector(t) = sigma * sqrt(4 t log(T/alpha))`. Factor
√2 vs `phiTilt` matches the √2 in the ranking
`etaVector = √2 · etaHR`. -/
noncomputable def phiTiltVector (sigma : ℝ) (alpha : ℝ) (T : ℕ) : ℝ :=
  if T = 0 then 0 else
    Real.sqrt (4 * Real.log ((T : ℝ) / alpha) / (sigma^2 * T))

noncomputable def phiProcessVector
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} (M : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω =>
    let lam := phiTiltVector sigma alpha T
    Real.exp (lam * M t ω - lam^2 * sigma^2 * t / 2)

lemma phiTiltVector_nonneg (sigma alpha : ℝ) (T : ℕ) : 0 ≤ phiTiltVector sigma alpha T := by
  unfold phiTiltVector; positivity

lemma phiProcessVector_eq_ratio (sigma alpha : ℝ) (T : ℕ) {Ω : Type*} (M : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    phiProcessVector sigma alpha T M t ω =
      Real.exp (phiTiltVector sigma alpha T * M t ω) /
        Real.exp (phiTiltVector sigma alpha T ^ 2 * sigma ^ 2 * t / 2) := by
  unfold phiProcessVector; rw [← Real.exp_sub]

lemma phiProcessVector_zero_ae_eq_one
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (M : ℕ → Ω → ℝ)
    (hM0 : M 0 =ᵐ[μ] 0) :
    (fun ω => phiProcessVector sigma alpha T M 0 ω) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  filter_upwards [hM0] with ω hω using by simp +decide [hω, phiProcessVector]

lemma integral_phiProcessVector_zero_eq_one
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (hM0 : M 0 =ᵐ[μ] 0) :
    ∫ ω, phiProcessVector sigma alpha T M 0 ω ∂μ = 1 := by
  convert MeasureTheory.integral_const (1 : ℝ) using 1
  rw [MeasureTheory.integral_congr_ae]
  · exact phiProcessVector_zero_ae_eq_one sigma alpha T M hM0
  · simp +decide [MeasureTheory.measureReal_def]

lemma phiProcessVector_supermartingale
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG sigma 𝓕 μ) :
    Supermartingale (phiProcessVector sigma alpha T M.process) 𝓕 μ := by
  convert exp_process_is_supermartingale M (phiTiltVector sigma alpha T) (phiTiltVector_nonneg sigma alpha T) using 1
  exact funext fun t => funext fun ω => phiProcessVector_eq_ratio sigma alpha T M.process t ω

lemma phiProcessVector_nonneg (sigma alpha : ℝ) (T : ℕ) {Ω : Type*} (M : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ phiProcessVector sigma alpha T M t ω := by
  exact Real.exp_nonneg _

/-- **Phi-transform preserves admissibility, vector case.** Vector-
family analogue of `phi_transform_hr_admissible`: the exp-transform
at `phiTiltVector` preserves admissibility at `alpha`. -/
theorem phi_transform_vector_admissible
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1)
    (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG sigma 𝓕 μ)
    (hM0 : M.process 0 =ᵐ[μ] 0) :
    μ {ω | ∃ t ≤ 2^b,
            phiProcessVector sigma alpha (2^b) M.process t ω
              ≥ 1 / alpha}
      ≤ ENNReal.ofReal alpha := by
  -- Step 1: Rewrite ≥ to ≤ form matching ville_supermartingale
  have h_set_eq : {ω | ∃ t ≤ 2^b, phiProcessVector sigma alpha (2^b) M.process t ω ≥ 1 / alpha}
      = {ω | ∃ t : ℕ, t ≤ 2^b ∧ 1 / alpha ≤ phiProcessVector sigma alpha (2^b) M.process t ω} := by
    ext ω; simp only [ge_iff_le, Set.mem_setOf_eq]
  rw [h_set_eq]
  -- Step 2: Apply ville_supermartingale
  have h_sm := phiProcessVector_supermartingale sigma hσ alpha (2^b) M
  have h_nn : ∀ t ω, 0 ≤ phiProcessVector sigma alpha (2^b) M.process t ω :=
    phiProcessVector_nonneg sigma alpha (2^b) M.process
  have h_c_pos : (0 : ℝ) < 1 / alpha := div_pos one_pos halpha.1
  have h_ville := ville_supermartingale_finite h_sm h_nn h_c_pos (2^b)
  refine le_trans h_ville ?_
  -- Step 3: Simplify ∫ Y 0 / (1/alpha) = 1 / (1/alpha) = alpha
  rw [integral_phiProcessVector_zero_eq_one sigma alpha (2^b) M.process hM0]
  have halpha_pos := halpha.1
  have : 1 / (1 / alpha) = alpha := by field_simp
  rw [this]

/-! ## aCS-case Phi-transform (Aristotle target B) -/

/-- aCS-family optimised tilt: `c_aCS(t) = sigma * sqrt(2 t log(1/alpha))`
has `t`-invariant log term, so the tilt is `sqrt(2 log(1/alpha)/(σ²T))`. -/
noncomputable def phiTiltACS (sigma : ℝ) (alpha : ℝ) (T : ℕ) : ℝ :=
  if T = 0 then 0 else
    Real.sqrt (2 * Real.log (1 / alpha) / (sigma^2 * T))

noncomputable def phiProcessACS
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} (M : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω =>
    let lam := phiTiltACS sigma alpha T
    Real.exp (lam * M t ω - lam^2 * sigma^2 * t / 2)

/-- **Phi-transform preserves admissibility, aCS case.** -/
lemma phiTiltACS_nonneg (sigma alpha : ℝ) (T : ℕ) : 0 ≤ phiTiltACS sigma alpha T := by
  unfold phiTiltACS; positivity

lemma phiProcessACS_eq_ratio (sigma alpha : ℝ) (T : ℕ) {Ω : Type*} (M : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    phiProcessACS sigma alpha T M t ω =
      Real.exp (phiTiltACS sigma alpha T * M t ω) /
        Real.exp (phiTiltACS sigma alpha T ^ 2 * sigma ^ 2 * t / 2) := by
  unfold phiProcessACS; rw [← Real.exp_sub]

lemma phiProcessACS_zero_ae_eq_one
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (M : ℕ → Ω → ℝ)
    (hM0 : M 0 =ᵐ[μ] 0) :
    (fun ω => phiProcessACS sigma alpha T M 0 ω) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  filter_upwards [hM0] with ω hω using by simp +decide [hω, phiProcessACS]

lemma integral_phiProcessACS_zero_eq_one
    (sigma : ℝ) (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (hM0 : M 0 =ᵐ[μ] 0) :
    ∫ ω, phiProcessACS sigma alpha T M 0 ω ∂μ = 1 := by
  convert MeasureTheory.integral_const (1 : ℝ) using 1
  rw [MeasureTheory.integral_congr_ae]
  · exact phiProcessACS_zero_ae_eq_one sigma alpha T M hM0
  · simp +decide [MeasureTheory.measureReal_def]

lemma phiProcessACS_supermartingale
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (T : ℕ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG sigma 𝓕 μ) :
    Supermartingale (phiProcessACS sigma alpha T M.process) 𝓕 μ := by
  convert exp_process_is_supermartingale M (phiTiltACS sigma alpha T) (phiTiltACS_nonneg sigma alpha T) using 1
  exact funext fun t => funext fun ω => phiProcessACS_eq_ratio sigma alpha T M.process t ω

lemma phiProcessACS_nonneg (sigma alpha : ℝ) (T : ℕ) {Ω : Type*} (M : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ phiProcessACS sigma alpha T M t ω := by
  exact Real.exp_nonneg _

/-- **Phi-transform preserves admissibility, aCS case.** -/
theorem phi_transform_acs_admissible
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1)
    (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG sigma 𝓕 μ)
    (hM0 : M.process 0 =ᵐ[μ] 0) :
    μ {ω | ∃ t ≤ 2^b,
            phiProcessACS sigma alpha (2^b) M.process t ω
              ≥ 1 / alpha}
      ≤ ENNReal.ofReal alpha := by
  -- Step 1: Rewrite ≥ to ≤ form matching ville_supermartingale
  have h_set_eq : {ω | ∃ t ≤ 2^b, phiProcessACS sigma alpha (2^b) M.process t ω ≥ 1 / alpha}
      = {ω | ∃ t : ℕ, t ≤ 2^b ∧ 1 / alpha ≤ phiProcessACS sigma alpha (2^b) M.process t ω} := by
    ext ω; simp only [ge_iff_le, Set.mem_setOf_eq]
  rw [h_set_eq]
  -- Step 2: Apply ville_supermartingale
  have h_sm := phiProcessACS_supermartingale sigma hσ alpha (2^b) M
  have h_nn : ∀ t ω, 0 ≤ phiProcessACS sigma alpha (2^b) M.process t ω :=
    phiProcessACS_nonneg sigma alpha (2^b) M.process
  have h_c_pos : (0 : ℝ) < 1 / alpha := div_pos one_pos halpha.1
  have h_ville := ville_supermartingale_finite h_sm h_nn h_c_pos (2^b)
  refine le_trans h_ville ?_
  -- Step 3: Simplify ∫ Y 0 / (1/alpha) = 1 / (1/alpha) = alpha
  rw [integral_phiProcessACS_zero_eq_one sigma alpha (2^b) M.process hM0]
  have halpha_pos := halpha.1
  have : 1 / (1 / alpha) = alpha := by field_simp
  rw [this]

end Pythia
