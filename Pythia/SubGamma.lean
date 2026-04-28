/-
Pythia.SubGamma — tail-class generalisation of SubGaussianMG.

A sub-gamma random variable `X` with parameters `(ν, c)` has MGF
bounded by
    E[exp(λ X)] ≤ exp(ν λ² / (2 (1 - c λ)))
for `c |λ| < 1`.  Sub-Gaussian is the `c = 0` case (the condition
becomes `0 < 1`, always true, and the bound reduces to `ν λ² / 2`).

We define the conditional-MGF version (matching our SubGaussianMG
pattern) and state the analog of Ville's inequality under sub-gamma
tails.  The bound is weaker than sub-Gaussian at the tails — an
exponential rate `exp(-τ / c)` kicks in beyond the Gaussian regime —
but covers bounded random variables (which are sub-gamma with
`c = b` for magnitude bound `b`).
-/

import Mathlib
import Pythia.Basic
import Pythia.SubGaussianMG
import Pythia.Tactic.Pythia

namespace Pythia

open MeasureTheory ProbabilityTheory

/-- A sub-gamma martingale with parameters `(ν, c)`: an adapted
process whose increments have conditional MGF bounded by
`exp(ν λ² / (2 (1 - c λ)))` for `c * |λ| < 1`, plus integrability
+ zero conditional mean.  Generalises `SubGaussianMG`; setting
`c = 0` recovers the sub-Gaussian bound.

Note: the condition `c * |λ| < 1` replaces the mathematically
equivalent `|λ| < 1/c` to avoid the Lean convention `1 / (0 : ℝ) = 0`,
which would make the MGF bound vacuously true when `c = 0`. -/
structure SubGammaMG
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (ν c : ℝ) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] where
  process : ℕ → Ω → ℝ
  adapted : Adapted 𝓕 process
  integrable : ∀ t, Integrable (process t) μ
  integrable_exp : ∀ t : ℕ, ∀ lam : ℝ, c * |lam| < 1 →
    Integrable (fun ω => Real.exp (lam * process t ω)) μ
  increments_exp_integrable : ∀ t : ℕ, ∀ lam : ℝ, c * |lam| < 1 →
    Integrable (fun ω => Real.exp (lam * (process (t + 1) ω - process t ω))) μ
  /-- Conditional MGF bound: $\mathbb{E}_\mu[e^{\lambda \Delta_t} \mid
  \mathcal{F}_t] \leq e^{\nu \lambda^2 / (2 (1 - c \lambda))}$ almost
  surely, for every non-negative `λ` with `c * λ < 1`. -/
  increments_subGamma : ∀ t : ℕ, ∀ lam : ℝ, 0 ≤ lam → c * lam < 1 →
    ∀ᵐ ω ∂μ,
      (μ[fun ω' => Real.exp (lam *
        (process (t + 1) ω' - process t ω')) | 𝓕 t]) ω ≤
      Real.exp (ν * lam^2 / (2 * (1 - c * lam)))
  increments_zero_mean : ∀ t,
    μ[fun ω => process (t + 1) ω - process t ω | 𝓕 t] =ᵐ[μ] 0
  nu_pos : 0 < ν
  c_nonneg : 0 ≤ c

/-
A sub-Gaussian martingale with parameter `σ` is a sub-gamma
martingale with `(ν, c) = (σ², 0)`.  When `c = 0`, the condition
`c * |λ| < 1` reduces to `0 < 1` (always true), so the MGF bound
`exp(σ² λ²/2)` must hold for all `λ`.
-/
@[stat_lemma]
theorem SubGaussianMG_to_SubGammaMG
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (M : SubGaussianMG σ 𝓕 μ) :
    Nonempty (SubGammaMG (σ^2) 0 𝓕 μ) := by
  refine' ⟨ ⟨ M.process, M.adapted, M.integrable, fun t lam _ => _, _, _, M.increments_zero_mean, _, _ ⟩ ⟩;
  · exact M.integrable_exp t lam;
  · intro t lam _;
    convert M.increments_subG t |> fun h => h.integrable_exp_mul lam using 1;
  · intro t lam hlam_nonneg hlam_bound;
    have := M.increments_subG t;
    convert this.ae_condExp_le lam using 1;
    rw [ Real.coe_toNNReal _ ( sq_nonneg σ ) ] ; ring;
  · exact sq_pos_of_pos M.sigma_pos;
  · norm_num

/-- The exponential process `exp(λ M_t) / exp(K t)` where
`K = ν λ² / (2(1 - cλ))` is a supermartingale under the sub-gamma
@[stat_lemma]
MGF bound. -/
theorem exp_subGamma_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {ν c : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (M : SubGammaMG ν c 𝓕 μ) (lam : ℝ) (hlam_pos : 0 < lam)
    (hlam_bound : c * lam < 1) :
    Supermartingale
      (fun t ω => Real.exp (lam * M.process t ω) /
                  Real.exp (ν * lam ^ 2 / (2 * (1 - c * lam)) * ↑t))
      𝓕 μ := by
  set K := ν * lam ^ 2 / (2 * (1 - c * lam)) with hK_def
  set Y : ℕ → Ω → ℝ := fun t ω =>
      Real.exp (lam * M.process t ω) / Real.exp (K * ↑t) with hY_def
  have hlam' : c * |lam| < 1 := by rwa [abs_of_pos hlam_pos]
  have hlam_nonneg : 0 ≤ lam := hlam_pos.le
  have hK_pos : 0 < K := by
    apply div_pos (mul_pos M.nu_pos (sq_pos_of_pos hlam_pos))
    exact mul_pos two_pos (sub_pos.mpr hlam_bound)
  -- Non-negativity
  have hY_nonneg : ∀ t ω, 0 ≤ Y t ω := fun t ω =>
    div_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  -- Measurability
  have hexp_meas : ∀ t, Measurable[𝓕 t] (fun ω => Real.exp (lam * M.process t ω)) := by
    intro t; exact Real.measurable_exp.comp ((M.adapted t).const_mul lam)
  have hY_meas : ∀ t, Measurable[𝓕 t] (Y t) := by
    intro t; exact (hexp_meas t).div measurable_const
  have hY_strMeas : ∀ t, StronglyMeasurable[𝓕 t] (Y t) := fun t =>
    (hY_meas t).stronglyMeasurable
  have hY_adapted : StronglyAdapted 𝓕 Y := hY_strMeas
  -- Integrability
  have hY_int : ∀ t, Integrable (Y t) μ := by
    intro t
    have h_exp_int := M.integrable_exp t lam hlam'
    have : Y t = fun ω => (Real.exp (K * ↑t))⁻¹ * Real.exp (lam * M.process t ω) := by
      funext ω; simp only [Y, div_eq_inv_mul]
    rw [this]; exact h_exp_int.const_mul _
  -- One-step bound
  refine MeasureTheory.supermartingale_nat (E := ℝ) hY_adapted hY_int ?_
  intro t
  set ΔM : Ω → ℝ := fun ω => M.process (t + 1) ω - M.process t ω with hΔM_def
  set eK : ℝ := Real.exp K with heK_def
  have heK_pos : 0 < eK := Real.exp_pos _
  -- MGF bound
  have h_subG_bound :
      ∀ᵐ ω ∂μ, (μ[fun ω' => Real.exp (lam * ΔM ω') | 𝓕 t]) ω ≤ eK :=
    M.increments_subGamma t lam hlam_nonneg hlam_bound
  -- g = exp(lam * ΔM) / eK
  set g : Ω → ℝ := fun ω => Real.exp (lam * ΔM ω) / eK with hg_def
  -- Factor: Y(t+1) = Y t * g
  have h_factor : ∀ ω, Y (t + 1) ω = Y t ω * g ω := by
    intro ω
    simp only [Y, g, ΔM]
    have h_sum : lam * M.process (t + 1) ω
        = lam * M.process t ω + lam * (M.process (t + 1) ω - M.process t ω) := by ring
    have h_exp_sum :
        Real.exp (lam * M.process (t + 1) ω)
          = Real.exp (lam * M.process t ω)
            * Real.exp (lam * (M.process (t + 1) ω - M.process t ω)) := by
      rw [h_sum, Real.exp_add]
    have h_exp_denom :
        Real.exp (K * ((↑t : ℝ) + 1))
          = Real.exp (K * ↑t) * Real.exp K := by
      rw [show K * ((↑t : ℝ) + 1) = K * ↑t + K from by ring, Real.exp_add]
    rw [h_exp_sum]
    push_cast
    rw [h_exp_denom]
    simp only [heK_def]
    field_simp
  -- g integrability
  have h_g_int : Integrable g μ := by
    have h_exp_int := M.increments_exp_integrable t lam hlam'
    have : g = fun ω => eK⁻¹ * Real.exp (lam * ΔM ω) := by
      funext ω; simp only [g, div_eq_inv_mul]
    rw [this]; exact h_exp_int.const_mul _
  -- Y*g integrability
  have h_Yg_int : Integrable (fun ω => Y t ω * g ω) μ := by
    have : (fun ω => Y t ω * g ω) = Y (t + 1) := by funext ω; exact (h_factor ω).symm
    rw [this]; exact hY_int _
  -- Pull-out
  have h_pull :
      μ[fun ω => Y t ω * g ω | 𝓕 t] =ᵐ[μ] fun ω => Y t ω * (μ[g | 𝓕 t]) ω :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left (hY_strMeas t) h_Yg_int h_g_int
  -- g = eK⁻¹ • exp(lam * ΔM)
  have h_g_eq : g = (eK⁻¹ : ℝ) • fun ω => Real.exp (lam * ΔM ω) := by
    funext ω; simp only [g, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have h_condExp_g :
      μ[g | 𝓕 t] =ᵐ[μ] (eK⁻¹ : ℝ) • μ[fun ω => Real.exp (lam * ΔM ω) | 𝓕 t] := by
    rw [h_g_eq]; exact MeasureTheory.condExp_smul (eK⁻¹) _ _
  -- Bound μ[g | F_t] ≤ 1
  have h_g_le_one : ∀ᵐ ω ∂μ, (μ[g | 𝓕 t]) ω ≤ 1 := by
    filter_upwards [h_condExp_g, h_subG_bound] with ω hcg hbd
    rw [hcg]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc eK⁻¹ * (μ[fun ω' => Real.exp (lam * ΔM ω') | 𝓕 t]) ω
        ≤ eK⁻¹ * eK := mul_le_mul_of_nonneg_left hbd (le_of_lt (inv_pos.mpr heK_pos))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt heK_pos)
  -- Combine
  have h_Yeq : Y (t + 1) = fun ω => Y t ω * g ω := by funext ω; exact h_factor ω
  have h_condExp_Yt1 :
      μ[Y (t + 1) | 𝓕 t] =ᵐ[μ] fun ω => Y t ω * (μ[g | 𝓕 t]) ω := by
    rw [h_Yeq]; exact h_pull
  filter_upwards [h_condExp_Yt1, h_g_le_one] with ω hcond hbnd
  rw [hcond]
  calc Y t ω * (μ[g | 𝓕 t]) ω
      ≤ Y t ω * 1 := mul_le_mul_of_nonneg_left hbnd (hY_nonneg t ω)
    _ = Y t ω := mul_one _

/-
Ville's inequality for sub-gamma martingales: crossing probability
is bounded by `exp(-τ²/(2 ν N + 2 c τ))` (the sub-gamma tail form).
For bounded increments (sub-gamma with `c = b`), this is sharper than
Hoeffding for small τ and matches the Bennett-Bernstein bound for
@[stat_lemma]
larger τ.
-/
theorem subGamma_ville_ineq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {ν c : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (M : SubGammaMG ν c 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * ν * N + 2 * c * τ))) := by
  -- Show that the chosen λ satisfies the conditions for the exponential supermartingale.
  have h_lambda_pos : 0 < τ / (ν * N + c * τ) := by
    exact div_pos hτ ( add_pos_of_pos_of_nonneg ( mul_pos M.nu_pos ( Nat.cast_pos.mpr hN ) ) ( mul_nonneg M.c_nonneg hτ.le ) )
  have h_lambda_bound : c * (τ / (ν * N + c * τ)) < 1 := by
    rw [ mul_div, div_lt_iff₀ ] <;> nlinarith [ M.nu_pos, show ( N : ℝ ) ≥ 1 by norm_cast, M.c_nonneg ];
  -- Define K and Y as in the provided solution.
  set lam := τ / (ν * N + c * τ)
  set K := ν * lam ^ 2 / (2 * (1 - c * lam))
  set Y := fun t ω => Real.exp (lam * M.process t ω) / Real.exp (K * t);
  -- Step 2 - Event containment: Show μ {∃ t ≤ N, M_t ≥ τ} ≤ μ {∃ t ≤ N, exp(lam*τ - K*N) ≤ Y t ω}.
  have h_event_containment : μ {ω | ∃ t ≤ N, M.process t ω ≥ τ} ≤ μ {ω | ∃ t ≤ N, Real.exp (lam * τ - K * N) ≤ Y t ω} := by
    refine' MeasureTheory.measure_mono _;
    intro ω hω
    obtain ⟨t, ht₁, ht₂⟩ := hω
    use t, ht₁
    have h_exp : Real.exp (lam * M.process t ω) / Real.exp (K * t) ≥ Real.exp (lam * τ - K * N) := by
      rw [ ← Real.exp_sub ] ; exact Real.exp_le_exp.mpr ( by nlinarith [ show ( t : ℝ ) ≤ N by norm_cast, show ( 0 : ℝ ) ≤ K by exact div_nonneg ( mul_nonneg ( le_of_lt ( M.nu_pos ) ) ( sq_nonneg _ ) ) ( mul_nonneg zero_le_two ( sub_nonneg.mpr h_lambda_bound.le ) ) ] ) ;
    exact h_exp;
  -- Step 3 - Apply ville_supermartingale_finite with threshold = exp(lam*τ - K*N) > 0.
  have h_ville : μ {ω | ∃ t ≤ N, Real.exp (lam * τ - K * N) ≤ Y t ω} ≤ ENNReal.ofReal ((∫ ω, Y 0 ω ∂μ) / Real.exp (lam * τ - K * N)) := by
    apply ville_supermartingale_finite;
    any_goals positivity;
    convert exp_subGamma_supermartingale M lam h_lambda_pos ( by linarith ) using 1;
    exact fun t ω => div_nonneg ( Real.exp_nonneg _ ) ( Real.exp_nonneg _ );
  -- Step 4 - Compute ∫ Y_0 = 1.
  have h_integral_Y0 : ∫ ω, Y 0 ω ∂μ = 1 := by
    simp +zetaDelta at *;
    rw [ MeasureTheory.integral_congr_ae ( hM0.mono fun ω hω => by rw [ hω ] ) ] ; norm_num;
  refine' le_trans h_event_containment ( h_ville.trans _ );
  rw [ h_integral_Y0, one_div, ← Real.exp_neg ];
  rw [ show - ( lam * τ - K * N ) = -τ ^ 2 / ( 2 * ν * N + 2 * c * τ ) from _ ];
  grind

end Pythia