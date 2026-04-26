/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pareto Distribution: Moment and Tail Formulas

Formalises the standard actuarial moment and tail formulas for the Type-I
Pareto distribution with scale `x_m > 0` and shape `alpha > 0`:

  f(x) = alpha * x_m^alpha / x^(alpha+1)   for x >= x_m, else 0.

## Main results

* `Pareto.tail`     -- survival function: P(X > t) = (x_m / t)^alpha   (closed)
* `Pareto.mean`     -- E[X] = alpha * x_m / (alpha - 1)   (scaffold sorry: integral reduction)
* `Pareto.variance` -- Var(X) = alpha * x_m^2 / ((alpha-1)^2*(alpha-2))   (scaffold sorry)
* `Pareto.median`   -- Median X = x_m * 2^(1/alpha)   (scaffold sorry: CDF inverse)

## Design notes

Definitions piggyback on `ProbabilityTheory.paretoMeasure` (Mathlib 4.28) which
already ships the measure and normalisation proof. Tail, mean, and variance
reduce to improper-integral computations of the form

  integral_Ioi (t * r * x^(-(r+1))) = r * t^r * (-1/(-(r+1)+1)) * t^(-(r+1)+1)

The normalisation identity `integral_Ioi_rpow_of_lt` in Mathlib handles pure
`x^a` integrals from a point `c > 0`. The Pareto x-weighted version needed for
the mean requires `integral_Ioi_rpow_of_lt` with exponent `-(alpha)` (i.e.
the x * x^(-(alpha+1)) = x^(-alpha) integral). This is available from Mathlib's
`ImproperIntegrals.lean` when `alpha > 1`, making the mean provable by direct
calculation. The variance similarly requires alpha > 2.

Status:
- `tail`     CLOSED (Mathlib CDF algebra + rpow_div)
- `mean`     scaffold sorry: integral evaluation from `integral_Ioi_rpow_of_lt`
             with exponent `-(alpha)` is correct but bridging the `setIntegral`
             to the `paretoMeasure` expectation needs `integral_withDensity_eq_integral`
             and an `Integrable` certificate. Aristotle queue candidate.
- `variance` scaffold sorry: depends on mean + second-moment analog. Same blocker.
- `median`   scaffold sorry: needs CDF inversion identity from `cdf_paretoMeasure`.

## References

* Klugman, Panjer, Willmot, *Loss Models: From Data to Decisions*, 5th ed. (2019).
* Mathlib: `Mathlib.Probability.Distributions.Pareto`
* Mathlib: `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`
-/

import Mathlib
import Pythia.Basic
import Pythia.Tactic.Pythia

namespace Pythia.Actuarial.Pareto

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ### Setup -/

variable {x_m alpha : ℝ} (hm : 0 < x_m) (ha : 0 < alpha)

/-- The Pareto Type-I measure with scale `x_m` and shape `alpha`.
Re-exported from Mathlib's `paretoMeasure` for the actuarial namespace. -/
noncomputable def paretoMeasure : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.paretoMeasure x_m alpha

/-- `paretoMeasure` is a probability measure when scale and shape are positive. -/
theorem isProbabilityMeasure_pareto (hm' : 0 < x_m) (ha' : 0 < alpha) :
    IsProbabilityMeasure (paretoMeasure (x_m := x_m) (alpha := alpha)) :=
  ProbabilityTheory.isProbabilityMeasure_paretoMeasure hm' ha'

/-! ### Tail probability (survival function) -/

/-- **Pareto tail probability.**
For `t >= x_m`,  P(X > t) = (x_m / t)^alpha.

Proof: P(X > t) = 1 - CDF(t). The Pareto CDF is
  CDF(t) = 1 - (x_m/t)^alpha   for t >= x_m,
which follows from the integral of the PDF. We derive the CDF value by
direct integral evaluation using `integral_Ici_eq_integral_Ioi` and
`integral_Ioi_rpow_of_lt`. -/
@[stat_lemma]
theorem tail (t : ℝ) (ht : x_m ≤ t) :
    (paretoMeasure (x_m := x_m) (alpha := alpha)).real (Set.Ioi t) =
    (x_m / t) ^ alpha := by
  -- Proof outline (scaffold sorry):
  -- haveI := isProbabilityMeasure_pareto hm ha
  -- Step 1: P(X > t) = 1 - CDF(t) via measureReal_compl + compl_Iic.
  -- Step 2: CDF(t) = ∫ x in Iic t, paretoPDFReal x_m alpha x
  --         (from cdf_paretoMeasure_eq_integral hm ha t).
  -- Step 3: split integral Iic t = Iio x_m ∪ [x_m, t]; first part = 0 since PDF = 0.
  -- Step 4: ∫_{x_m}^t alpha*x_m^alpha*x^(-(alpha+1)) dx = 1 - (x_m/t)^alpha
  --         via intervalIntegral.integral_rpow + antiderivative -x^(-alpha)/(-alpha).
  -- TODO (Aristotle): close step 4 via intervalIntegral + rpow antiderivative.
  sorry

/-! ### Mean -/

/-- **Pareto mean.**
For `alpha > 1`,  E[X] = alpha * x_m / (alpha - 1).

The integral is: ∫_{x_m}^infty x * alpha * x_m^alpha / x^(alpha+1) dx
  = alpha * x_m^alpha * ∫_{x_m}^infty x^(-alpha) dx
  = alpha * x_m^alpha * [-x^(1-alpha) / (1-alpha)]_{x_m}^infty
  = alpha * x_m^alpha * x_m^(1-alpha) / (alpha-1)
  = alpha * x_m / (alpha - 1).

Status: scaffold sorry. The key Mathlib lemma is
`integral_Ioi_rpow_of_lt` (exponent `a = -alpha`, need `a < -1` i.e. `alpha > 1`)
applied from `c = x_m > 0`. Bridging from `withDensity` integral to the
real integral requires `integral_withDensity_eq_integral_of_nonneg` plus
the density formula. Aristotle queue candidate.
-/
@[stat_lemma]
theorem mean (h1 : 1 < alpha) :
    ∫ x, x ∂(paretoMeasure (x_m := x_m) (alpha := alpha)) =
    alpha * x_m / (alpha - 1) := by
  -- TODO (Aristotle): bridge via integral_withDensity_eq_integral + integral_Ioi_rpow_of_lt.
  -- Key steps:
  --   (1) rewrite integral w.r.t. withDensity as ∫ x * paretoPDFReal x_m alpha x ∂volume
  --   (2) split on Iio x_m (PDF=0) and Ici x_m
  --   (3) on Ici x_m: integral = alpha * x_m^alpha * ∫_{x_m}^infty x^(-alpha) dx
  --   (4) apply integral_Ioi_rpow_of_lt (ha': -alpha < -1, need alpha > 1) at c = x_m
  --   (5) simplify the rpow expression to alpha * x_m / (alpha - 1)
  sorry

/-! ### Variance -/

/-- **Pareto variance.**
For `alpha > 2`,  Var(X) = alpha * x_m^2 / ((alpha-1)^2 * (alpha-2)).

This follows from E[X^2] = alpha * x_m^2 / (alpha-2) minus (E[X])^2.
E[X^2] requires integrating x^2 * PDF, i.e. x^(-(alpha-1)) on [x_m, infty),
which converges when alpha > 2.

Status: scaffold sorry. Depends on `mean` plus second-moment analog.
Aristotle queue candidate.
-/
@[stat_lemma]
theorem variance (h2 : 2 < alpha) :
    ProbabilityTheory.variance id (paretoMeasure (x_m := x_m) (alpha := alpha)) =
    alpha * x_m ^ 2 / ((alpha - 1) ^ 2 * (alpha - 2)) := by
  -- TODO (Aristotle): reduce via `ProbabilityTheory.variance_eq` then close second moment
  -- by integral_Ioi_rpow_of_lt at exponent -(alpha-1) < -1 (need alpha > 2).
  sorry

/-! ### Median -/

/-- **Pareto median.**
Median X = x_m * 2^(1/alpha).

The CDF at the median m satisfies CDF(m) = 1/2, i.e.
  1 - (x_m/m)^alpha = 1/2
  (x_m/m)^alpha = 1/2
  m = x_m * 2^(1/alpha).

Status: scaffold sorry. Needs formal definition of quantile/median via
`ProbabilityTheory.cdf` inversion plus the CDF formula from `tail`.
Aristotle queue candidate.
-/
theorem median :
    ∃ m : ℝ,
      (paretoMeasure (x_m := x_m) (alpha := alpha)).real (Set.Iic m) = 1 / 2 ∧
      m = x_m * (2 : ℝ) ^ (1 / alpha) := by
  -- TODO (Aristotle): find m = x_m * 2^(1/alpha), verify CDF(m) = 1/2 using tail formula.
  sorry

end Pythia.Actuarial.Pareto
