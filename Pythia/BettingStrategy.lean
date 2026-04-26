/-
Pythia.BettingStrategy — wealth-process machinery for betting
confidence sequences.

The betting family of anytime-valid CS uses a wealth process `W_t`
defined by a bounded adaptive strategy `λ_t : Ω → ℝ` with
`|λ_t| ≤ B` for some `B` tied to the sub-Gaussian parameter.  The
wealth `W_t = Π_{s ≤ t} (1 + λ_s (X_s - μ))` is a nonnegative
martingale under the null `X_s ~ (mean μ)` hypothesis.  This is the
object Ville's inequality is applied to in
Waudby-Smith and Ramdas 2024.

Mathlib has `MeasureTheory.Martingale` but no strategy / wealth
abstractions.  We supply them here.
-/

import Mathlib

import Pythia.Basic

namespace Pythia

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A bounded adaptive betting strategy: a sequence of `𝓕_t`-adapted
real-valued weights with a uniform magnitude bound `B ≥ 0`.  Used to
define a wealth process in the Waudby-Smith / Ramdas 2024 betting
construction. -/
structure BettingStrategy
    (𝓕 : Filtration ℕ mΩ) (B : ℝ) where
  /-- The adaptive weight at each step. -/
  lam : ℕ → Ω → ℝ
  /-- Adaptedness of the weight process to the filtration. -/
  adapted : Adapted 𝓕 lam
  /-- Uniform magnitude bound on the weight process. -/
  bound : ∀ t ω, |lam t ω| ≤ B

/-- One-step wealth update: `w ↦ w · (1 + λ · ξ)`. -/
@[simp]
noncomputable def wealthStep (w lam xi : ℝ) : ℝ := w * (1 + lam * xi)

/-- Wealth process induced by a `BettingStrategy` against a centred
increment process `ξ_t`.  Defined by `W_0 ≡ 1` and
`W_{t+1} ω = W_t ω · (1 + λ_t ω · ξ_t ω)`.  Recursive definition on
ℕ. -/
noncomputable def wealthProcess
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 1
  | (t + 1), ω => wealthProcess σ ξ t ω * (1 + σ.lam t ω * ξ t ω)

@[simp]
lemma wealthProcess_zero
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ) (ω : Ω) :
    wealthProcess σ ξ 0 ω = 1 := rfl

@[simp]
lemma wealthProcess_succ
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    wealthProcess σ ξ (t + 1) ω =
      wealthProcess σ ξ t ω * (1 + σ.lam t ω * ξ t ω) := rfl

/-- Non-negativity of the wealth process under the strategy /
increment bound.  When `|λ_t ω · ξ_t ω| < 1`, the one-step factor
`1 + λ_t ω · ξ_t ω` is positive, and a product of positives is
non-negative by induction. -/
theorem wealthProcess_nonneg
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound : ∀ t ω, |σ.lam t ω * ξ t ω| < 1) :
    ∀ t ω, 0 ≤ wealthProcess σ ξ t ω := by
  intro t ω
  induction t with
  | zero => simp
  | succ n ih =>
    rw [wealthProcess_succ]
    have h1 : (0 : ℝ) ≤ 1 + σ.lam n ω * ξ n ω := by
      have := (abs_lt.mp (h_bound n ω)).1
      linarith
    exact mul_nonneg ih h1

/-
The wealth process is strongly adapted to the filtration.
-/
private lemma wealthProcess_stronglyAdapted
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_xi_adapted : Adapted 𝓕 ξ) :
    StronglyAdapted 𝓕 (wealthProcess σ ξ) := by
  have := σ.adapted;
  intro t;
  induction' t with t ih;
  · exact stronglyMeasurable_const;
  · have h_step : StronglyMeasurable[𝓕 (t + 1)] (fun ω => 1 + σ.lam t ω * ξ t ω) := by
      have h_step : StronglyMeasurable[𝓕 t] (fun ω => σ.lam t ω * ξ t ω) := by
        exact StronglyMeasurable.mul ( this t |> Measurable.stronglyMeasurable ) ( h_xi_adapted t |> Measurable.stronglyMeasurable );
      exact StronglyMeasurable.add ( stronglyMeasurable_const ) ( h_step.mono ( 𝓕.mono ( Nat.le_succ _ ) ) );
    convert ih.mono ( 𝓕.mono ( Nat.le_succ t ) ) |> fun h => h.mul h_step using 1

/-
One-step martingale property: `wealthProcess σ ξ t =ᵐ[μ] μ[wealthProcess σ ξ (t+1) | 𝓕 t]`.
-/
private lemma wealthProcess_condExp_succ
    {𝓕 : Filtration ℕ mΩ} [IsFiniteMeasure μ] {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound : ∀ t ω, |σ.lam t ω * ξ t ω| < 1)
    (h_xi_adapted : Adapted 𝓕 ξ)
    (h_integrable : ∀ t, Integrable (ξ t) μ)
    (h_wealth_integrable : ∀ t, Integrable (wealthProcess σ ξ t) μ)
    (h_zero_mean : ∀ t, μ[(ξ t) | 𝓕 t] =ᵐ[μ] 0)
    (t : ℕ) :
    wealthProcess σ ξ t =ᵐ[μ] μ[wealthProcess σ ξ (t + 1) | 𝓕 t] := by
  -- By definition of $W_{t+1}$, we have $W_{t+1} = W_t + W_t \lambda_t \xi_t$.
  have h_W_succ : ∀ ω, wealthProcess σ ξ (t + 1) ω = wealthProcess σ ξ t ω + (wealthProcess σ ξ t ω * σ.lam t ω * ξ t ω) := by
    intro ω; rw [ show wealthProcess σ ξ ( t + 1 ) ω = wealthProcess σ ξ t ω * ( 1 + σ.lam t ω * ξ t ω ) by rfl ] ; ring;
  have h_cond_exp : μ[(wealthProcess σ ξ t) * σ.lam t * ξ t | 𝓕 t] =ᶠ[ae μ] (wealthProcess σ ξ t) * σ.lam t * μ[ξ t | 𝓕 t] := by
    apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
    · refine' StronglyMeasurable.mul _ _;
      · have := wealthProcess_stronglyAdapted σ ξ h_xi_adapted;
        exact this t;
      · have := σ.adapted t;
        exact this.stronglyMeasurable;
    · have h_integrable_prod : Integrable (wealthProcess σ ξ (t + 1)) μ := by
        exact h_wealth_integrable _;
      convert h_integrable_prod.sub ( h_wealth_integrable t ) using 1 ; ext ω ; aesop;
  have h_cond_exp : μ[wealthProcess σ ξ (t + 1) | 𝓕 t] =ᵐ[μ] μ[wealthProcess σ ξ t | 𝓕 t] + μ[(wealthProcess σ ξ t) * σ.lam t * ξ t | 𝓕 t] := by
    rw [ show wealthProcess σ ξ ( t + 1 ) = wealthProcess σ ξ t + wealthProcess σ ξ t * σ.lam t * ξ t from funext h_W_succ ];
    apply_rules [ MeasureTheory.condExp_add ];
    have h_integrable_prod : Integrable (wealthProcess σ ξ (t + 1)) μ := by
      exact h_wealth_integrable _;
    convert h_integrable_prod.sub ( h_wealth_integrable t ) using 1 ; ext ω ; simp +decide [ h_W_succ ];
    ring;
  have h_cond_exp : μ[wealthProcess σ ξ t | 𝓕 t] =ᵐ[μ] wealthProcess σ ξ t := by
    have h_cond_exp : StronglyMeasurable[𝓕 t] (wealthProcess σ ξ t) := by
      have := wealthProcess_stronglyAdapted σ ξ h_xi_adapted;
      exact this t;
    rw [ MeasureTheory.condExp_of_stronglyMeasurable ];
    · exact h_cond_exp;
    · exact h_wealth_integrable t;
  have h_cond_exp : μ[(wealthProcess σ ξ t) * σ.lam t * ξ t | 𝓕 t] =ᵐ[μ] 0 := by
    filter_upwards [ ‹μ[wealthProcess σ ξ t * σ.lam t * ξ t | 𝓕 t] =ᶠ[ae μ] wealthProcess σ ξ t * σ.lam t * μ[ξ t | 𝓕 t]›, h_zero_mean t ] with ω hω₁ hω₂ using by aesop;
  filter_upwards [ ‹μ[wealthProcess σ ξ ( t + 1 ) | 𝓕 t] =ᶠ[ae μ] μ[wealthProcess σ ξ t | 𝓕 t] + μ[wealthProcess σ ξ t * σ.lam t * ξ t | 𝓕 t]›, ‹μ[wealthProcess σ ξ t | 𝓕 t] =ᶠ[ae μ] wealthProcess σ ξ t›, h_cond_exp ] with ω hω₁ hω₂ hω₃ using by aesop;

/-- Under the null hypothesis (zero conditional mean of `ξ_t` given
`𝓕_t`) the wealth process is a martingale.  Proof uses the pull-out
property of conditional expectation on the `𝓕_t`-measurable factor
`W_t`, then applies the zero-conditional-mean hypothesis on `ξ_t`. -/
theorem wealthProcess_martingale
    {𝓕 : Filtration ℕ mΩ} [IsFiniteMeasure μ] {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound : ∀ t ω, |σ.lam t ω * ξ t ω| < 1)
    (h_xi_adapted : Adapted 𝓕 ξ)
    (h_integrable : ∀ t, Integrable (ξ t) μ)
    (h_wealth_integrable : ∀ t, Integrable (wealthProcess σ ξ t) μ)
    (h_zero_mean : ∀ t, μ[(ξ t) | 𝓕 t] =ᵐ[μ] 0) :
    Martingale (wealthProcess σ ξ) 𝓕 μ := by
  exact martingale_nat
    (wealthProcess_stronglyAdapted σ ξ h_xi_adapted)
    h_wealth_integrable
    (wealthProcess_condExp_succ σ ξ h_bound h_xi_adapted h_integrable h_wealth_integrable h_zero_mean)

/-- Log-wealth is the natural object for the Ville-type anytime-valid
bound.  `logWealthProcess σ ξ t ω := Real.log (wealthProcess σ ξ t ω)`
is well-defined on the positivity event (Lemma
`wealthProcess_nonneg`).  When the wealth is strictly positive it is
the running sum of `Real.log (1 + λ_s ω · ξ_s ω)` for `s < t`. -/
noncomputable def logWealthProcess
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.log (wealthProcess σ ξ t ω)

end Pythia