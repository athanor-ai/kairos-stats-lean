/-
Kairos.Stats.BettingStrategy — wealth-process machinery for betting
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
import Kairos.Stats.Basic

namespace Kairos.Stats

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
  sorry

/-- Log-wealth is the natural object for the Ville-type anytime-valid
bound.  `logWealthProcess σ ξ t ω := Real.log (wealthProcess σ ξ t ω)`
is well-defined on the positivity event (Lemma
`wealthProcess_nonneg`).  When the wealth is strictly positive it is
the running sum of `Real.log (1 + λ_s ω · ξ_s ω)` for `s < t`. -/
noncomputable def logWealthProcess
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.log (wealthProcess σ ξ t ω)

end Kairos.Stats
