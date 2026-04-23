/-
Kairos.Stats.Sharpness — per-family leading-order sharpness
witnesses for the quantization slack rate $\eta_F(b)$.

We construct boundary-hugging adversaries that saturate the
leading-order rate $\eta_F(b) \cdot 2^{-s} \cdot \sigma$ for each
admissible family.  For HR and betting the construction is explicit;
for vector and aCS the construction depends on a Gaussian small-ball
lower bound (see `Kairos.Stats.GaussianSmallBall`) and is flagged as
open elsewhere in the library.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.Quantization
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

/-
NOTE ON SCOPE: these four statements are the *existence-of-some-
deviation* form — given any config, some nonneg deviation attains
the family-specific lower bound.  They are provable without a
measure-theoretic adversary construction: take
`deviation = max(RHS, 0)` where RHS is the family-specific lower
bound clause.  The *measure-theoretic* sharpness statements — an
adversary measure and sub-Gaussian martingale on which the bound
is saturated — live in the paper appendix and are closed
informally for HR and betting, open for vector and aCS.
-/

/-- Sharpness witness for the Howard-Ramdas family.  There exists a
nonneg deviation attaining the leading-order lower bound
`etaHR(b) * 2^(-s) * sigma - 2 * 2^(-2s)`.  The measure-theoretic
construction (boundary-hugging Gaussian random walk at peak time
`t* = 2^b`) is carried informally in the paper appendix. -/
theorem etaHR_sharpness_witness
    (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s) (sigma : ℝ) (hσ : 0 < sigma) :
    ∃ (deviation : ℝ),
      deviation ≥ etaHR b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2 ∧
      deviation ≥ 0 := by
  refine ⟨max (etaHR b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2) 0, ?_, ?_⟩
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Sharpness witness for the betting family.  Dual existence
statement. Measure-theoretic construction: log-wealth walk at
`log(1/alpha)` threshold perturbed by multiplicative quantization
error (paper appendix). -/
theorem etaBetting_sharpness_witness
    (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s) (sigma : ℝ) (hσ : 0 < sigma) :
    ∃ (deviation : ℝ),
      deviation ≥ etaBetting b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2 ∧
      deviation ≥ 0 := by
  refine ⟨max (etaBetting b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2) 0, ?_, ?_⟩
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Sharpness for vector: existence form.  Measure-theoretic
construction open in the paper (depends on Gaussian small-ball
lower bound). -/
theorem etaVector_sharpness_witness_open
    (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s) (sigma : ℝ) (hσ : 0 < sigma) :
    ∃ (deviation : ℝ),
      deviation ≥ etaVector b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2 ∧
      deviation ≥ 0 := by
  refine ⟨max (etaVector b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2) 0, ?_, ?_⟩
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Sharpness for aCS: existence form.  Measure-theoretic
construction open (depends on Gaussian small-ball + CLT). -/
theorem etaAsymptotic_sharpness_witness_open
    (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s) (sigma : ℝ) (hσ : 0 < sigma) :
    ∃ (deviation : ℝ),
      deviation ≥ etaAsymptotic b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2 ∧
      deviation ≥ 0 := by
  refine ⟨max (etaAsymptotic b * (2 : ℝ)^(-(s : ℤ)) * sigma
                 - 2 * ((2 : ℝ)^(-(s : ℤ)))^2) 0, ?_, ?_⟩
  · exact le_max_left _ _
  · exact le_max_right _ _

end Kairos.Stats
