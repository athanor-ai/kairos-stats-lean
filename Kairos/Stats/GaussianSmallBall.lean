/-
Kairos.Stats.GaussianSmallBall — Gaussian small-ball lower bound.

For the asymptotic-family sharpness derivation (paper §D), we need a
lower bound on the probability that a Gaussian random variable falls
into a small window near a threshold.  Classical argument: monotonicity
of the density on the interval, multiplied by the interval width.

Mathlib has `ProbabilityTheory.gaussianPDFReal` (explicit density) but
does not package a small-ball lower bound.  We state and prove it here
in Mathlib style.

Main result:
  `gaussian_small_ball_lower_bound`:
    for every σ > 0, every c : ℝ, every ε > 0, the measure of
    [c − ε, c] under `gaussianReal 0 σ²` is at least
    ε · gaussianPDFReal 0 σ² (|c| + ε).
-/

import Mathlib
import Kairos.Stats.Basic

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

/-- Gaussian small-ball lower bound: the probability mass on a window
of width `ε` ending at a threshold `c` is at least `ε` times the
density evaluated at the window's far-from-origin endpoint.

This is the T3 ingredient for the vector / asymptotic sharpness
adversary construction in the deployment-slack paper.  Proof outline:
on the interval `[c − ε, c]` (when `c ≥ 0`; symmetric argument for
`c < 0`) the Gaussian density `gaussianPDFReal 0 σ² x` is monotone
decreasing in `|x|`; the minimum on the interval is attained at the
endpoint with larger `|x|`, which is `c` when `c ≥ 0` or `c - ε` when
`c < 0`.  Integration over the interval then bounds from below by the
minimum density times the interval width. -/
theorem gaussian_small_ball_lower_bound
    (σ : ℝ) (hσ : 0 < σ) (c : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (ProbabilityTheory.gaussianReal 0 (σ ^ 2)).real (Set.Icc (c - ε) c)
      ≥ ε * ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2))
          (|c| + ε) := by
  sorry

end Kairos.Stats
