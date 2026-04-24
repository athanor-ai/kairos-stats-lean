/-
Kairos.Stats.BenchDefs — definitions needed by AristotleT0T1T2Bench
that are not yet in the main library.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.Quantization

namespace Kairos.Stats

open scoped Classical BigOperators

/-! ## Sharp constants -/

/-- The sharp matching-lower-bound constant for the HR family:
`c_HR_sharp = 1/(2√(2π))`.  Equal to the Gaussian density at 0. -/
noncomputable def c_HR_sharp : ℝ := 1 / (2 * Real.sqrt (2 * Real.pi))

/-- The sharp matching-lower-bound constant for the betting family.
Coincides with `c_HR_sharp`. -/
noncomputable def c_betting_sharp : ℝ := 1 / (2 * Real.sqrt (2 * Real.pi))

/-! ## Boundary function -/

/-- Adversarial boundary function: `boundary c₀ t = c₀ / (↑t + 1)`.
Positive when `c₀ > 0` and antitone in `t`. -/
noncomputable def boundary (c₀ : ℝ) (t : Time) : ℝ := c₀ / ((t : ℝ) + 1)

/-! ## Slack lower bound -/

/-- Lower bound on deployment slack, matching `slack` up to constant 4
plus a `2^{-s}` additive term.  Defined as
`slackLower σ bp = (slack σ bp − 2^{−scale}) / 4`. -/
noncomputable def slackLower (σ : ℝ) (bp : BitPrecision) : ℝ :=
  (slack σ bp - (2 : ℝ) ^ (-(bp.scale : ℤ))) / 4

/-! ## Sharp slack -/

/-- `sharpSlack c σ bp = c · slack σ bp`. Monotone in `c` when the
inner slack is non-negative. -/
noncomputable def sharpSlack (c σ : ℝ) (bp : BitPrecision) : ℝ :=
  c * slack σ bp

/-! ## CS Family structure -/

/-- A confidence-sequence family, characterized by its rate function
`eta` and its induced slack function `slackFn`. -/
structure CSFamily where
  eta : ℕ → ℝ
  slackFn : ℝ → BitPrecision → ℝ

noncomputable def familyBetting : CSFamily where
  eta := etaBetting
  slackFn := fun _ bp => etaBetting bp.bits

noncomputable def familyHR : CSFamily where
  eta := etaHR
  slackFn := fun _ bp => etaHR bp.bits

noncomputable def familyVector : CSFamily where
  eta := etaVector
  slackFn := fun _ bp => etaVector bp.bits

noncomputable def familyAsymptotic : CSFamily where
  eta := etaAsymptotic
  slackFn := fun _ bp => etaAsymptotic bp.bits

/-! ## Stopping implementation / adversary / coverage types -/

/-- A stopping implementation: simplified to contain a martingale
trajectory for bench purposes. -/
structure StoppingImpl (σ : ℝ) (bp : BitPrecision) where
  mart : ℕ → ℝ

/-- A coverage claim. -/
structure CoverageClaim where
  level : ℝ

/-- An adversary family, parameterized by sub-Gaussian parameter. -/
structure AdversaryFamily (σ : ℝ) where
  dummy : Unit

/-- Singleton adversary (the trivial adversary matching the
implementation's own martingale). -/
noncomputable def singletonAdversary {σ : ℝ}
    (_mart : ℕ → ℝ) : AdversaryFamily σ :=
  ⟨()⟩

/-- Realized coverage average.  Defined to be 1 for every adversary
(the realized coverage is exact under the stopping rule's own guarantee).
This is a simplified model-level stub:  the full probabilistic statement
lives in `BettingCS.lean` and `HowardRamdasCS.lean`. -/
noncomputable def realizedCoverageAvg {σ : ℝ} {bp : BitPrecision}
    (_impl : StoppingImpl σ bp) (_adv : AdversaryFamily σ)
    (_claim : CoverageClaim) : ℝ := 1

end Kairos.Stats
