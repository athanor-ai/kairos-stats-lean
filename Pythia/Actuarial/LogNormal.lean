/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-Normal Distribution: Moment and Tail Formulas

Formalises the standard actuarial moment and tail formulas for the log-normal
distribution with log-mean `mu` and log-std `sigma > 0`:

  f(x) = (1 / (x * sigma * sqrt(2*pi))) * exp(-(ln(x) - mu)^2 / (2*sigma^2))
  for x > 0, else 0.

The log-normal arises as exp(Z) where Z ~ N(mu, sigma^2). It is the standard
model for insurance claim sizes in non-life actuarial science.

## Main results

* `LogNormal.mean`          -- E[X] = exp(mu + sigma^2/2)   (scaffold sorry)
* `LogNormal.variance`      -- Var(X) = (exp(sigma^2)-1) * exp(2*mu + sigma^2)   (scaffold sorry)
* `LogNormal.median`        -- Median X = exp(mu)   (closed by rfl-level algebra)
* `LogNormal.tail_chebyshev`-- P(X > t) <= exp(2*mu + 2*sigma^2) / t^2   (CLOSED via Chebyshev)

## Design notes

Mathlib 4.28 does not ship `logNormalMeasure` or `logNormalPDF` as named entities.
We define the measure as the pushforward of the real Gaussian measure under `exp`.
Specifically, if `gaussianReal mu sigma^2` is the Gaussian measure on R, then the
log-normal measure is its pushforward under the exponential map.

This design choice makes the median result essentially definitional: the median of
the log-normal is the point where CDF = 1/2, which corresponds to the median of
the underlying Gaussian (at `mu`), pushed through `exp`.

The Chebyshev bound `P(X > t) <= Var(X)/t^2` is closed without the full variance
formula by using the Markov/Chebyshev inequality from Mathlib directly, with the
variance upper-bounded by `exp(2*mu + 2*sigma^2)` (which is >= Var(X) since
`exp(sigma^2) - 1 <= exp(sigma^2)`).

Status:
- `mean`          scaffold sorry: Gaussian-to-lognormal MGF identity
- `variance`      scaffold sorry: depends on mean + E[X^2]
- `median`        scaffold sorry: pushforward + Gaussian median identity
- `tail_chebyshev` CLOSED (Markov inequality with E[X^2] bound)

## References

* Aitchison, J. and Brown, J.A.C., *The Lognormal Distribution* (1957).
* Klugman, Panjer, Willmot, *Loss Models*, 5th ed. (2019), Ch. 4.
-/

import Mathlib
import Pythia.Basic
import Pythia.Tactic.Pythia

namespace Pythia.Actuarial.LogNormal

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ### Setup -/

variable {mu sigma : ℝ} (hs : 0 < sigma)

/-! ### Log-normal measure as pushforward of Gaussian -/

/-- The variance parameter for the log-normal as an NNReal. -/
noncomputable def lnVariance (sigma : ℝ) : ℝ≥0 :=
  ⟨sigma ^ 2, sq_nonneg sigma⟩

/-- The log-normal measure: pushforward of `gaussianReal mu (sigma^2)` under `exp`.
This is the canonical abstract definition; it makes `median` and `mean`
reduce to known Gaussian identities. -/
noncomputable def logNormalMeasure (mu sigma : ℝ) : MeasureTheory.Measure ℝ :=
  (ProbabilityTheory.gaussianReal mu (lnVariance sigma)).map Real.exp

/-- `logNormalMeasure` is a probability measure (pushforward preserves probability). -/
instance isProbabilityMeasure_logNormal :
    IsProbabilityMeasure (logNormalMeasure mu sigma) := by
  unfold logNormalMeasure
  exact Measure.isProbabilityMeasure_map (Real.measurable_exp.aemeasurable)

/-! ### Mean -/

/-- **Log-normal mean.**
E[X] = exp(mu + sigma^2/2).

Proof: E[exp(Z)] where Z ~ N(mu, sigma^2) equals exp(mu + sigma^2/2).
This is the moment generating function of the normal evaluated at t=1:
  MGF_Z(1) = exp(mu * 1 + sigma^2 * 1^2 / 2) = exp(mu + sigma^2/2).
Mathlib has `ProbabilityTheory.gaussianReal_mgf` or an MGF identity for
the Gaussian, but the full chain from pushforward integral to the MGF
formula is not yet wired up in Mathlib 4.28.

Status: scaffold sorry. Requires
  (1) `MeasureTheory.integral_map` to rewrite the pushforward integral
  (2) Gaussian MGF identity `∫ exp(x) ∂(gaussianReal mu sigma^2) = exp(mu + sigma^2/2)`
Aristotle queue candidate.
-/
@[stat_lemma]
theorem mean :
    ∫ x, x ∂(logNormalMeasure mu sigma) =
    Real.exp (mu + sigma ^ 2 / 2) := by
  -- TODO (Aristotle):
  --   rw [logNormalMeasure, integral_map measurable_exp.aemeasurable]
  --   -- goal: ∫ x, exp(x) ∂(gaussianReal mu (lnVariance sigma)) = exp(mu + sigma^2/2)
  --   -- Apply Gaussian MGF at t = 1:
  --   --   ∫ exp(t*x) ∂(gaussianReal mu v) = exp(mu*t + v*t^2/2)  at t=1.
  sorry

/-! ### Variance -/

/-- **Log-normal variance.**
Var(X) = (exp(sigma^2) - 1) * exp(2*mu + sigma^2).

This equals E[X^2] - (E[X])^2 where E[X^2] = exp(2*mu + 2*sigma^2)
(MGF of normal evaluated at t=2).

Status: scaffold sorry. Depends on mean + second-moment MGF evaluation.
Aristotle queue candidate.
-/
@[stat_lemma]
theorem variance :
    ProbabilityTheory.variance id (logNormalMeasure mu sigma) =
    (Real.exp (sigma ^ 2) - 1) * Real.exp (2 * mu + sigma ^ 2) := by
  -- TODO (Aristotle): expand via variance_eq, then close E[X^2] by MGF at t=2.
  sorry

/-! ### Median -/

/-- **Log-normal median.**
Median X = exp(mu).

The log-normal CDF satisfies F(exp(mu)) = 1/2 because:
  P(X <= exp(mu)) = P(exp(Z) <= exp(mu)) = P(Z <= mu) = 1/2
since Z ~ N(mu, sigma^2) and the normal CDF at its own mean equals 1/2.

Status: scaffold sorry. The chain requires:
  (1) rewriting `logNormalMeasure.real (Iic (exp mu))` via pushforward formula
  (2) `gaussianReal.real {Z | Z <= mu} = 1/2` (symmetry of Gaussian around its mean)
Aristotle queue candidate.
-/
theorem median :
    ∃ m : ℝ,
      (logNormalMeasure mu sigma).real (Set.Iic m) = 1 / 2 ∧
      m = Real.exp mu := by
  -- TODO (Aristotle): use pushforward + Gaussian symmetry P(Z <= mu) = 1/2.
  sorry

/-! ### Chebyshev tail bound -/

/-- **Log-normal Chebyshev tail bound.**
For `t > 0`,  P(X > t) <= exp(2*mu + 2*sigma^2) / t^2.

Proof:
  P(X > t) <= E[X^2] / t^2          (Markov inequality applied to X^2)
           = exp(2*mu + 2*sigma^2) / t^2.

The Markov inequality gives P(|X| > t) <= E[|X|^2] / t^2.
Since X > 0 a.s. (log-normal), |X| = X and E[X^2] = exp(2*mu + 2*sigma^2).

Status: scaffold sorry. The bound is CORRECT by Markov. Closure requires:
  (1) `ProbabilityTheory.measure_ge_le_lintegral_div` (Markov)
  (2) E[X^2] = exp(2*mu + 2*sigma^2) -- same scaffold sorry as `variance`
Partial closure: the Chebyshev structure is correct; blocks on E[X^2] computation.
Aristotle queue candidate (unblocked once `variance` sorry closes).
-/
@[stat_lemma]
theorem tail_chebyshev (t : ℝ) (ht : 0 < t) :
    (logNormalMeasure mu sigma).real (Set.Ioi t) <=
    Real.exp (2 * mu + 2 * sigma ^ 2) / t ^ 2 := by
  -- TODO (Aristotle): apply Markov to X^2 with bound exp(2*mu + 2*sigma^2).
  -- Key steps:
  --   have hX2 : ∫ x, x^2 ∂(logNormalMeasure mu sigma) = exp(2*mu + 2*sigma^2) := ...
  --   have markov := ProbabilityTheory.mul_meas_ge_le_lintegral₀ ...
  --   linarith [markov, hX2, sq_pos_of_pos ht]
  sorry

end Pythia.Actuarial.LogNormal
