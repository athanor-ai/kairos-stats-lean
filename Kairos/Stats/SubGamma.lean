/-
Kairos.Stats.SubGamma — tail-class generalisation of SubGaussianMG.

A sub-gamma random variable `X` with parameters `(ν, c)` has MGF
bounded by
    E[exp(λ X)] ≤ exp(ν λ² / (2 (1 - c λ)))
for `|λ| < 1 / c`.  Sub-Gaussian is the `c = 0` case (taking the
limit: `ν λ² / 2`).

We define the conditional-MGF version (matching our SubGaussianMG
pattern) and state the analog of Ville's inequality under sub-gamma
tails.  The bound is weaker than sub-Gaussian at the tails — an
exponential rate `exp(-τ / c)` kicks in beyond the Gaussian regime —
but covers bounded random variables (which are sub-gamma with
`c = b` for magnitude bound `b`).
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

/-- A sub-gamma martingale with parameters `(ν, c)`: an adapted
process whose increments have conditional MGF bounded by
`exp(ν λ² / (2 (1 - c λ)))` for `|λ| < 1 / c`, plus integrability
+ zero conditional mean.  Generalises `SubGaussianMG`; setting
`c = 0` recovers the sub-Gaussian bound. -/
structure SubGammaMG
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (ν c : ℝ) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] where
  process : ℕ → Ω → ℝ
  adapted : Adapted 𝓕 process
  integrable : ∀ t, Integrable (process t) μ
  /-- Conditional MGF bound: $\mathbb{E}_\mu[e^{\lambda \Delta_t} \mid
  \mathcal{F}_t] \leq e^{\nu \lambda^2 / (2 (1 - c \lambda))}$ almost
  surely, for every `|λ| < 1 / c`. -/
  increments_subGamma : ∀ t : ℕ, ∀ lam : ℝ, |lam| < 1 / c →
    ∀ᵐ ω ∂μ,
      (μ[fun ω' => Real.exp (lam *
        (process (t + 1) ω' - process t ω')) | 𝓕 t]) ω ≤
      Real.exp (ν * lam^2 / (2 * (1 - c * lam)))
  increments_zero_mean : ∀ t,
    μ[fun ω => process (t + 1) ω - process t ω | 𝓕 t] =ᵐ[μ] 0
  nu_pos : 0 < ν
  c_nonneg : 0 ≤ c

/-- A sub-Gaussian martingale with parameter `σ` is a sub-gamma
martingale with `(ν, c) = (σ², 0)`.  This gives a clean embedding of
`SubGaussianMG` into `SubGammaMG` at the cost of the strict
inequality constraint `|λ| < 1 / c` becoming vacuous (all `λ`
allowed). -/
theorem SubGaussianMG_to_SubGammaMG
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (M : SubGaussianMG σ 𝓕 μ) :
    Nonempty (SubGammaMG (σ^2) 0 𝓕 μ) := by
  sorry

/-- Ville's inequality for sub-gamma martingales: crossing probability
is bounded by `exp(-τ²/(2 ν N + 2 c τ))` (the sub-gamma tail form).
For bounded increments (sub-gamma with `c = b`), this is sharper than
Hoeffding for small τ and matches the Bennett-Bernstein bound for
larger τ. -/
theorem subGamma_ville_ineq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {ν c : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (M : SubGammaMG ν c 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * ν * N + 2 * c * τ))) := by
  sorry

end Kairos.Stats
