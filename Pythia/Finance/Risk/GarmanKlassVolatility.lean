/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Garman-Klass Volatility Estimator Kernel

The Garman-Klass (1980) estimator uses OHLC (open, high, low, close)
data to produce a more efficient variance estimator than the classical
close-to-close estimator.  Given log-price relatives measured from the
open

    h = log(High / Open),   l = log(Low / Open),   c = log(Close / Open),

the GK variance kernel is

    gkVariance(h, l, c) = (1/2) * (h - l)^2 - (2 * log 2 - 1) * c^2.

The range term `(1/2) * (h - l)^2` is the Parkinson (1980) variance
kernel; the correction `-(2 * log 2 - 1) * c^2` adjusts for the
overnight drift (close-to-close component).  The coefficient
`2 * log 2 - 1 ≈ 0.386` is derived from the theoretical optimality
calculation in Garman-Klass (1980), Equation (3.4).

## Main results

* `gkVariance`                        : kernel definition
* `gkVariance_zero`                   : gkVariance 0 0 0 = 0
* `gkVariance_range_term_nonneg`      : range term (1/2)*(h-l)^2 ≥ 0
* `gkVariance_sym_range`              : symmetric in (h, l) swap
* `gkVariance_mono_range`             : monotone in range (h-l)^2 for fixed c
* `gkVariance_parkinson_at_zero_close`: at c = 0 reduces to Parkinson kernel
* `gkVariance_ge_neg_correction`      : estimator ≥ negative correction term

## Why this lemma

The GK estimator achieves roughly 7.4x efficiency over the
close-to-close estimator under a geometric Brownian motion model,
making it the de-facto daily variance kernel on low-frequency
equity-vol desks.  Surfacing the algebraic kernel in Pythia gives
the `pythia` tactic cascade a closure target for range-based
volatility identities: monotonicity checks, Parkinson specialisation,
and lower-bound sanity tests.

## References

* Garman, M. B. and Klass, M. J.
  "On the Estimation of Security Price Volatilities from Historical Data."
  *Journal of Business* 53(1): 67-78 (1980).
* Parkinson, M.
  "The Extreme Value Method for Estimating the Variance of the Rate
   of Return."
  *Journal of Business* 53(1): 61-65 (1980).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Garman-Klass variance kernel for a single OHLC bar.

Arguments are log-price relatives from the open:
- `h`: log(High / Open)
- `l`: log(Low / Open)
- `c`: log(Close / Open)

The formula `(1/2) * (h - l)^2 - (2 * Real.log 2 - 1) * c^2` follows
Garman-Klass (1980), Equation (3.4), after setting the open log-return
to zero (measuring all prices relative to the open). -/
noncomputable def gkVariance (h l c : ℝ) : ℝ :=
  (1 / 2) * (h - l) ^ 2 - (2 * Real.log 2 - 1) * c ^ 2

/-- **Zero at zero.** All log-price relatives equal to zero (bar with
no price movement) gives zero variance. -/
@[stat_lemma]
theorem gkVariance_zero : gkVariance 0 0 0 = 0 := by
  unfold gkVariance; ring

/-- **Range term non-negativity.** The Parkinson range component
`(1/2) * (h - l)^2` is non-negative for all `h l : ℝ`. -/
@[stat_lemma]
theorem gkVariance_range_term_nonneg (h l : ℝ) :
    0 ≤ (1 / 2) * (h - l) ^ 2 := by
  exact mul_nonneg (by norm_num) (sq_nonneg _)

/-- **Symmetry in range.** Swapping high and low leaves the GK
variance unchanged:

    gkVariance h l c = gkVariance l h c.

This follows because `(h - l)^2 = (l - h)^2` is a ring identity. -/
@[stat_lemma]
theorem gkVariance_sym_range (h l c : ℝ) :
    gkVariance h l c = gkVariance l h c := by
  unfold gkVariance; ring

/-- **Monotone in range.** For fixed close log-return `c`, a larger
squared range produces a larger GK variance estimate:

    (h₁ - l₁)^2 ≤ (h₂ - l₂)^2  →  gkVariance h₁ l₁ c ≤ gkVariance h₂ l₂ c. -/
@[stat_lemma]
theorem gkVariance_mono_range {h₁ l₁ h₂ l₂ c : ℝ}
    (h : (h₁ - l₁) ^ 2 ≤ (h₂ - l₂) ^ 2) :
    gkVariance h₁ l₁ c ≤ gkVariance h₂ l₂ c := by
  unfold gkVariance
  have hle : (1 / 2) * (h₁ - l₁) ^ 2 ≤ (1 / 2) * (h₂ - l₂) ^ 2 :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  linarith

/-- **Parkinson specialisation.** When the close equals the open
(`c = 0`), the GK estimator reduces to the Parkinson (1980)
range-based variance kernel:

    gkVariance h l 0 = (1/2) * (h - l)^2. -/
@[stat_lemma]
theorem gkVariance_parkinson_at_zero_close (h l : ℝ) :
    gkVariance h l 0 = (1 / 2) * (h - l) ^ 2 := by
  unfold gkVariance; ring

/-- **Lower bound by correction term.** The GK estimator is at least
as large as the negative of the drift correction term:

    gkVariance h l c ≥ -(2 * Real.log 2 - 1) * c^2.

This holds because the range component `(1/2) * (h - l)^2` is
non-negative (by `gkVariance_range_term_nonneg`), so adding it to the
correction can only increase the estimate. -/
@[stat_lemma]
theorem gkVariance_ge_neg_correction (h l c : ℝ) :
    -(2 * Real.log 2 - 1) * c ^ 2 ≤ gkVariance h l c := by
  unfold gkVariance
  linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg (h - l))]

end Pythia.Finance
