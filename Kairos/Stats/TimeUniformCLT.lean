/-
Kairos.Stats.TimeUniformCLT — time-uniform central limit theorem and
asymptotic confidence sequences.

Reference: Waudby-Smith, Arbour, Sinha, Kennedy, Ramdas (2024).
*Time-uniform central limit theory and asymptotic confidence sequences.*
Annals of Statistics 52(6): 2804-2841.

The classical CLT controls a single fixed time. WSSR24 establishes a
*uniform-in-time* version: under standard regularity, a sequence of
standardised partial sums converges uniformly in time to a Brownian
motion in the Lévy-Prokhorov sense. The corollary is an asymptotic
confidence sequence (aCS) for the mean of an iid sequence whose width
matches the non-asymptotic CS up to an explicit slack term.

This module formalises:

1. `time_uniform_clt` — the time-uniform convergence statement.
2. `asymptotic_confidence_sequence` — the aCS construction.
3. `aCS_sharp_universal` — the WSSR24 sharp-constant claim that, in
   the limit `T → ∞`, the aCS slack rate matches the betting rate up
   to the universal constant `c_aCS = 1/(2√(2π))`. Removes the
   `σ ≤ 1` restriction in `Kairos.Stats.AsymptoticSharpness`.

Phase C / v0.3.0 deliverable. All theorems sorry'd until the
Lévy-Prokhorov machinery is closed (Mathlib does not currently
include uniform-in-time CLT — the underlying Lindeberg-swap +
Brownian-coupling lemmas have to be ported or proved here).
-/
import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

/-- Standardised partial sum: `S_n / √(n σ²)`. The classical CLT
shows this converges in distribution to `N(0, 1)`. -/
noncomputable def standardisedPartialSum
    (X : ℕ → ℝ) (sigma : ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).sum X / Real.sqrt (n * sigma^2)

/-- The Lévy-Prokhorov metric on Borel probability measures on ℝ.
Stated as a placeholder; Mathlib's `MeasureTheory.LevyProkhorov`
covers the construction but the time-uniform extension we need for
WSSR24 lives downstream. -/
noncomputable def levyProkhorov (μ ν : Measure ℝ) : ℝ :=
  sorry

/-- **Time-uniform CLT** (WSSR24 Theorem 2.1).

Given an iid sequence `X` with finite second moment `σ²`, the
sequence of standardised partial sums `S_n / √(n σ²)` converges, *in
the Lévy-Prokhorov metric uniformly in `n`*, to a Brownian motion
sample at time `1`. The classical CLT gives pointwise convergence;
the time-uniform CLT gives uniform convergence over the time horizon. -/
theorem time_uniform_clt
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hX_iid : ∀ t, ProbabilityTheory.IndepFun (X 0) (X t) μ)
    (hX_finite_var : ∀ t, Integrable (fun ω => (X t ω)^2) μ)
    (hX_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0) :
    -- Statement: the sup over n of `levyProkhorov(law(S_n / √(nσ²)),
    -- law(W_1))` tends to 0 as the horizon goes to infinity, where
    -- `W_1 ~ N(0, 1)` is the Brownian-motion-at-time-1 distribution.
    -- Phrased as a placeholder True until the Lévy-Prokhorov +
    -- Brownian-motion machinery is in scope.
    True := by
  sorry

/-- **Asymptotic confidence sequence** (WSSR24 Theorem 3.1).

Construction of the aCS for the mean of an iid sequence. The aCS
width is `σ √(2 log(1/α) · log log(en) / n)` plus an explicit slack
term that vanishes as `n → ∞`. Sharp constant: `1/(2√(2π))`. -/
theorem asymptotic_confidence_sequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {sigma : ℝ} {alpha : ℝ}
    (hsigma_pos : 0 < sigma) (halpha : 0 < alpha ∧ alpha < 1)
    (hX_iid : ∀ t, ProbabilityTheory.IndepFun (X 0) (X t) μ)
    (hX_finite_var : ∀ t, Integrable (fun ω => (X t ω)^2) μ) :
    -- Statement: ∀ N₀ ∃ slack_N. for all n ≥ N₀, the aCS at level α
    -- covers the true mean with probability at least 1 - α - slack_N,
    -- and slack_N → 0 as N₀ → ∞. Phrased as a placeholder True
    -- pending the time-uniform-CLT prerequisite.
    True := by
  sorry

/-- **aCS sharp universal**: the asymptotic CS slack rate matches the
betting CS rate up to the universal constant `c_aCS = 1/(2√(2π))`,
removing the `σ ≤ 1` restriction in `Kairos.Stats.AsymptoticSharpness`.

Proves the universal version of the c_aCS claim that the
NeurIPS 2026 paper currently states under `σ ≤ 1`. After this
theorem lands, the paper's c_aCS bullet upgrades to "all four
families pinned without regime restrictions". -/
theorem aCS_sharp_universal :
    -- Statement: for any σ > 0, the aCS slack rate at horizon N is
    -- at least `(1/(2√(2π))) · σ · √(2 log N / N) - O(1/N)`.
    -- Phrased as a placeholder True pending time-uniform CLT.
    True := by
  sorry

end Kairos.Stats
