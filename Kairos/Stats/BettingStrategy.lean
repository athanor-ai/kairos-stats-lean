/-
Kairos.Stats.BettingStrategy — wealth-process machinery for betting
confidence sequences.

The betting family of anytime-valid CS uses a wealth process `W_t`
defined by a bounded adaptive strategy `λ_t : Ω → ℝ` with
`|λ_t| ≤ B` for some `B` that depends on the sub-Gaussian parameter.
The wealth `W_t = Π_{s ≤ t} (1 + λ_s (X_s - μ))` is a nonnegative
martingale with respect to the filtration and measure under the
null hypothesis.  This is the object Ville's inequality is applied
to in the Waudby-Smith and Ramdas 2024 construction.

Mathlib has `MeasureTheory.Martingale` but no strategy / wealth
abstractions.  We supply them here.
-/

import Mathlib
import Kairos.Stats.Basic

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A bounded adaptive betting strategy: a sequence of
`(ℱ_t)`-adapted real-valued functions `λ_t : Ω → ℝ` with a uniform
magnitude bound `B`.  Used to define a wealth process in the
Waudby-Smith / Ramdas 2024 betting construction. -/
structure BettingStrategy
    (𝓕 : Filtration ℕ mΩ) (B : ℝ) where
  /-- The adaptive weight at each step. -/
  lam : ℕ → Ω → ℝ
  /-- Adaptedness. -/
  adapted : Adapted 𝓕 lam
  /-- Uniform magnitude bound. -/
  bound : ∀ t ω, |lam t ω| ≤ B

/-- Wealth process induced by a `BettingStrategy` against a centred
increment process `ξ_t = X_t - μ`.  Defined as the running product
`W_0 = 1`, `W_{t+1} = W_t · (1 + λ_t · ξ_t)`.  Non-negativity requires
`|λ_t · ξ_t| < 1`, which follows from the strategy bound `B` and a
matching `|ξ_t| ≤ B^{-1}` assumption on the increments. -/
noncomputable def wealthProcess
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (List.range t).foldl
    (fun w s => w * (1 + σ.lam s ω * ξ s ω)) 1

/-- Under the null hypothesis the centred increment has conditional
expectation zero; the wealth process is then a martingale. -/
theorem wealthProcess_martingale
    {𝓕 : Filtration ℕ mΩ} [IsFiniteMeasure μ] {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound_xi : ∀ t ω, |ξ t ω| * B < 1)
    (h_integrable : ∀ t, Integrable (fun ω => ξ t ω) μ)
    (h_zero_mean : ∀ t, μ[(ξ t) | 𝓕 t] =ᵐ[μ] 0) :
    Martingale (wealthProcess σ ξ) 𝓕 μ := by
  sorry

/-- Non-negativity of the wealth process under the strategy / increment
bound. -/
theorem wealthProcess_nonneg
    {𝓕 : Filtration ℕ mΩ} {B : ℝ}
    (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound_xi : ∀ t ω, |ξ t ω| * B < 1) :
    ∀ t ω, 0 ≤ wealthProcess σ ξ t ω := by
  sorry

end Kairos.Stats
