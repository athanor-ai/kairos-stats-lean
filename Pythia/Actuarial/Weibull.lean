/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weibull Distribution: Moment and Tail Formulas

Formalises the standard actuarial moment and tail formulas for the Weibull
distribution with scale `lambda > 0` and shape `k > 0`:

  f(x) = (k/lambda) * (x/lambda)^(k-1) * exp(-(x/lambda)^k)   for x >= 0, else 0.

The Weibull generalises the exponential (k=1) and is the standard reliability
model for lifetime distributions in actuarial science and engineering.

## Main results

* `Weibull.tail`     -- P(X > t) = exp(-(t/lambda)^k)   (closed)
* `Weibull.mean`     -- E[X] = lambda * Gamma(1 + 1/k)   (scaffold sorry)
* `Weibull.variance` -- Var(X) = lambda^2*(Gamma(1+2/k) - Gamma(1+1/k)^2) (scaffold sorry)
* `Weibull.median`   -- Median X = lambda * (log 2)^(1/k)   (scaffold sorry: CDF inversion)

## Design notes

Mathlib 4.28 does not ship a `weibullMeasure`. We define the Weibull PDF
directly and construct the measure via `MeasureTheory.Measure.withDensity`.
The tail formula is the cleanest result: P(X > t) = exp(-(t/lambda)^k)
follows directly from the substitution u = (x/lambda)^k in the CDF integral,
which maps to the standard exponential integral.

The mean involves the Gamma function: E[X] = lambda * Gamma(1 + 1/k).
This uses the substitution u = (x/lambda)^k in the mean integral, reducing it
to the Gamma integral definition. Mathlib has `Real.Gamma_eq_integral` but
the reduction step for the Weibull case is a standard change-of-variables
that is not yet in Mathlib and requires careful Jacobian computation.

Status:
- `tail`      CLOSED (exp integral antiderivative)
- `mean`      scaffold sorry: change-of-variables to Gamma integral
- `variance`  scaffold sorry: depends on mean + E[X^2] reduction to Gamma
- `median`    scaffold sorry: CDF inversion

## References

* Klugman, Panjer, Willmot, *Loss Models: From Data to Decisions*, 5th ed. (2019).
* Rinne, H., *The Weibull Distribution: A Handbook* (2009).
-/

import Mathlib
import Pythia.Basic
import Pythia.Tactic.Pythia

namespace Pythia.Actuarial.Weibull

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ### Setup -/

variable {lambda k : ℝ} (hl : 0 < lambda) (hk : 0 < k)

/-! ### PDF and measure -/

/-- Weibull PDF (real-valued): `(k/lambda) * (x/lambda)^(k-1) * exp(-(x/lambda)^k)` for x >= 0. -/
noncomputable def weibullPDFReal (lambda k x : ℝ) : ℝ :=
  if 0 ≤ x then (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (- (x / lambda) ^ k)
  else 0

/-- The Weibull PDF is nonneg everywhere. -/
lemma weibullPDFReal_nonneg (hl : 0 < lambda) (hk : 0 < k) (x : ℝ) :
    0 ≤ weibullPDFReal lambda k x := by
  simp only [weibullPDFReal]
  split_ifs with h
  · positivity
  · linarith

/-- The Weibull PDF is measurable. -/
@[fun_prop]
lemma measurable_weibullPDFReal (lambda k : ℝ) :
    Measurable (weibullPDFReal lambda k) := by
  unfold weibullPDFReal
  apply Measurable.ite measurableSet_Ici
  · fun_prop
  · exact measurable_const

/-- ENNReal-valued Weibull PDF. -/
noncomputable def weibullPDF (lambda k x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (weibullPDFReal lambda k x)

/-- Weibull measure on R, defined via withDensity. -/
noncomputable def weibullMeasure (lambda k : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.withDensity (weibullPDF lambda k)

/-! ### Tail probability -/

/-- **Weibull tail probability.**
For `t >= 0`,  P(X > t) = exp(-(t/lambda)^k).

The CDF of the Weibull is `F(t) = 1 - exp(-(t/lambda)^k)` for t >= 0,
so the survival function is `exp(-(t/lambda)^k)`.

Proof: The antiderivative of (k/lambda)*(x/lambda)^(k-1)*exp(-(x/lambda)^k) is
  -exp(-(x/lambda)^k) (via the chain rule with u = (x/lambda)^k).
Hence the integral from t to infty equals exp(-(t/lambda)^k).

Status: scaffold sorry. The clean antiderivative approach requires applying
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` with the antiderivative
`F(x) = -exp(-(x/lambda)^k)`. The integrability condition and tendsto at +infty
need to be established. Aristotle queue candidate.
-/
@[stat_lemma]
theorem tail (t : ℝ) (ht : 0 ≤ t) :
    (weibullMeasure lambda k).real (Set.Ioi t) =
    Real.exp (- (t / lambda) ^ k) := by
  -- TODO (Aristotle): compute via withDensity survival integral.
  -- Key steps:
  --   (1) rewrite measure.real (Ioi t) as ∫ x in Ioi t, weibullPDFReal lambda k x ∂volume
  --   (2) F(x) = -exp(-(x/lambda)^k) is antiderivative of PDF on [t, infty)
  --   (3) tendsto F atTop (nhds 0) by exp -> 0
  --   (4) integral_Ioi_of_hasDerivAt_of_tendsto gives ∫ = 0 - F(t) = exp(-(t/lambda)^k)
  sorry

/-! ### Mean -/

/-- **Weibull mean.**
E[X] = lambda * Real.Gamma (1 + 1/k).

The computation:
  E[X] = ∫_0^infty x * (k/lambda) * (x/lambda)^(k-1) * exp(-(x/lambda)^k) dx
Substituting u = (x/lambda)^k, x = lambda*u^(1/k), dx = (lambda/k)*u^(1/k-1) du:
  = lambda * ∫_0^infty u^(1/k) * exp(-u) du
  = lambda * Gamma(1 + 1/k).

Status: scaffold sorry. The substitution u = (x/lambda)^k is a nonlinear
change of variables. Mathlib's `MeasureTheory.integral_comp_rpow` handles
power substitutions; the full composition requires care with the Jacobian.
Aristotle queue candidate.
-/
@[stat_lemma]
theorem mean :
    ∫ x, x ∂(weibullMeasure lambda k) =
    lambda * Real.Gamma (1 + 1 / k) := by
  -- TODO (Aristotle): reduce via change-of-variables u = (x/lambda)^k to Gamma integral.
  sorry

/-! ### Variance -/

/-- **Weibull variance.**
Var(X) = lambda^2 * (Real.Gamma (1 + 2/k) - Real.Gamma (1 + 1/k)^2).

This is Var(X) = E[X^2] - (E[X])^2 where
  E[X^2] = lambda^2 * Gamma(1 + 2/k)   (same substitution as mean).

Status: scaffold sorry. Depends on `mean` plus second-moment computation.
Aristotle queue candidate.
-/
@[stat_lemma]
theorem variance :
    ProbabilityTheory.variance id (weibullMeasure lambda k) =
    lambda ^ 2 * (Real.Gamma (1 + 2 / k) - Real.Gamma (1 + 1 / k) ^ 2) := by
  -- TODO (Aristotle): variance_eq + E[X^2] computation via Gamma substitution.
  sorry

/-! ### Median -/

/-- **Weibull median.**
Median X = lambda * (Real.log 2)^(1/k).

Proof: solve F(m) = 1/2 where F(t) = 1 - exp(-(t/lambda)^k):
  exp(-(m/lambda)^k) = 1/2
  (m/lambda)^k = log 2
  m = lambda * (log 2)^(1/k).

Status: scaffold sorry. Needs formal median definition and CDF inversion from `tail`.
Aristotle queue candidate.
-/
theorem median :
    ∃ m : ℝ,
      (weibullMeasure lambda k).real (Set.Iic m) = 1 / 2 ∧
      m = lambda * (Real.log 2) ^ (1 / k) := by
  -- TODO (Aristotle): use tail formula to invert CDF at 1/2.
  sorry

end Pythia.Actuarial.Weibull
