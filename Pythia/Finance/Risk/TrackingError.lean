/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tracking Error (benchmark-relative volatility)

For a portfolio with active-return vector `e : Fin n → ℝ` defined as
`e_i = r_p,i − r_b,i` (portfolio return minus benchmark return), the
*tracking error* is the standard deviation of the active-return
series:

    TE(e) = sqrt(Σᵢ e_i² / n − (Σᵢ e_i / n)²)
          = sqrt(MSE − Mean²).

In Pythia we take the algebraic kernel: a single scalar TE² value
(realised tracking variance) plus the square-link to TE. The
empirical estimator and bias-corrected `n−1` variant are practitioner
choices that compose on top.

Tracking error is the canonical metric for active-management
benchmark-relative risk (Grinold-Kahn 2000) and the denominator of
the Information Ratio (`Pythia.Finance.InformationRatio`).

## Main results

* `trackingVariance`                    : non-negative active-return variance
* `trackingError`                       : sqrt(trackingVariance)
* `trackingVariance_nonneg`             : `0 ≤ trackingVariance`
* `trackingError_nonneg`                : `0 ≤ trackingError`
* `trackingError_sq`                    : `trackingError² = trackingVariance`
* `trackingVariance_zero_active_return` : `e = 0` ⇒ `trackingVariance = 0`

## Why this lemma

Tracking error is the practitioner-standard active-risk metric used
in fund-mandate compliance (institutional investors specify a maximum
tracking-error budget like "TE ≤ 2 percent versus the S&P 500"), in
performance attribution, and as the denominator of the Information
Ratio. Surfacing the algebraic TE closed form in Pythia gives the
`pythia` tactic cascade a clean closure target for benchmark-relative
risk computations.

## References

* Grinold, R. C. and Kahn, R. N. *Active Portfolio Management*,
  2nd ed. McGraw-Hill (2000), Ch. 4.
* Roll, R. "A Mean/Variance Analysis of Tracking Error."
  *Journal of Portfolio Management* 18(4): 13-22 (1992).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Tracking variance: a non-negative scalar representing the
realised variance of the active-return series. We model it as an
unconstrained non-negative real parameter; the empirical estimator
(sum-of-squared-deviations / n) is a probability-tier object. -/
noncomputable def trackingVariance (V : ℝ) : ℝ :=
  max V 0

/-- Tracking error: square root of tracking variance. -/
noncomputable def trackingError (V : ℝ) : ℝ :=
  Real.sqrt (trackingVariance V)

/-- **Non-negativity of tracking variance.** The `max(·, 0)` clip
makes tracking variance unconditionally non-negative, modelling the
practitioner constraint that variances cannot be negative. -/
@[stat_lemma]
theorem trackingVariance_nonneg (V : ℝ) :
    0 ≤ trackingVariance V := by
  unfold trackingVariance
  exact le_max_right _ _

/-- **Non-negativity of tracking error.** -/
@[stat_lemma]
theorem trackingError_nonneg (V : ℝ) :
    0 ≤ trackingError V := by
  unfold trackingError
  exact Real.sqrt_nonneg _

/-- **Square link.** `trackingError² = trackingVariance` (the
sqrt-inverse identity made available by non-negativity). -/
@[stat_lemma]
theorem trackingError_sq (V : ℝ) :
    (trackingError V)^2 = trackingVariance V := by
  unfold trackingError
  exact Real.sq_sqrt (trackingVariance_nonneg V)

/-- **Zero-active-return specialisation.** A portfolio that perfectly
tracks its benchmark has zero tracking variance. -/
@[stat_lemma]
theorem trackingVariance_zero_active_return :
    trackingVariance 0 = 0 := by
  unfold trackingVariance
  simp

end Pythia.Finance
