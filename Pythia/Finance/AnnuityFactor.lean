/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous-Time Annuity Factor

The present value of a continuous annuity paying 1 unit per unit time
from `0` to `T` under continuously-compounded discount rate `r > 0` is

    a(r, T) = (1 - exp(-r·T)) / r.

This is the integral of the discount factor over `[0, T]`:
`∫₀ᵀ exp(-r·t) dt = (1 - exp(-r·T)) / r`. This file surfaces the
closed-form algebraic identity (no calculus); the integral link is
deferred to a calculus-tier file.

## Main results

* `continuousAnnuity`                  : `(1 - exp(-r·T)) / r`
* `continuousAnnuity_zero_time`        : `continuousAnnuity r 0 = 0`
* `continuousAnnuity_pos`              : `0 < a` when `r > 0`, `T > 0`
* `continuousAnnuity_lt_perpetuity`    : `a(r, T) < 1/r` for `r > 0`, `T > 0`
  (continuous-annuity present value is strictly less than the
  perpetuity limit `1/r`)

## Why this lemma

Mathlib has `Real.exp_pos`, `Real.exp_zero`, and `div_pos`, but no
named `annuity_factor` declaration.  Pythia surfaces the
continuous-annuity closed form so the `pythia` tactic cascade can
close DCF / fixed-income / amortisation goals without re-deriving it.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.2 (continuously-compounded annuity).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Continuous-time annuity present value:
    `a(r, T) = (1 - exp(-r·T)) / r`. -/
noncomputable def continuousAnnuity (r T : ℝ) : ℝ :=
  (1 - Real.exp (-(r * T))) / r

/-- **Boundary at `T = 0`.** The continuous annuity at zero horizon
has zero present value (no payments yet). -/
@[stat_lemma]
theorem continuousAnnuity_zero_time (r : ℝ) :
    continuousAnnuity r 0 = 0 := by
  unfold continuousAnnuity; simp [mul_zero, neg_zero, Real.exp_zero, sub_self, zero_div]

/-- **Positivity.** For positive rate and positive horizon, the
continuous-annuity present value is strictly positive. -/
@[stat_lemma]
theorem continuousAnnuity_pos {r T : ℝ} (hr : 0 < r) (hT : 0 < T) :
    0 < continuousAnnuity r T := by
  unfold continuousAnnuity
  apply div_pos _ hr
  have h_exp_lt_one : Real.exp (-(r * T)) < 1 := by
    have : -(r * T) < 0 := by nlinarith
    calc Real.exp (-(r * T)) < Real.exp 0 := Real.exp_lt_exp.mpr this
      _ = 1 := Real.exp_zero
  linarith

/-- **Strictly below perpetuity.** For any finite positive horizon,
the continuous-annuity value is strictly less than the perpetuity
limit `1/r`. -/
@[stat_lemma]
theorem continuousAnnuity_lt_perpetuity {r T : ℝ} (hr : 0 < r) (hT : 0 < T) :
    continuousAnnuity r T < 1 / r := by
  unfold continuousAnnuity
  rw [sub_div]
  have : 0 < Real.exp (-(r * T)) / r := div_pos (Real.exp_pos _) hr
  linarith

end Pythia.Finance
