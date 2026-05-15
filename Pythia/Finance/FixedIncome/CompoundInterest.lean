/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous Compound Interest

For principal `P`, continuously-compounded rate `r`, and time horizon
`t`, the account value at time `t` is

    A(P, r, t) = P · exp(r · t).

This is the continuous-time limit of the discrete compound-interest
formula `P · (1 + r/n)^(n·t)` as the compounding frequency `n → ∞`,
and is the standard convention used throughout quant finance (e.g.
risk-neutral discounting in the Black-Scholes framework).

## Main results

* `compoundContinuous`              : continuously-compounded account value `P · exp(r·t)`
* `compoundContinuous_pos`          : `0 < compoundContinuous P r t` when `P > 0`
* `compoundContinuous_zero_time`    : `compoundContinuous P r 0 = P`
* `compoundContinuous_monotone_t`   : monotone in `t` for `P ≥ 0`, `r ≥ 0`
* `compoundContinuous_exp_ge_one`   : `1 ≤ exp(r·t)` when `r·t ≥ 0`
  (compound factor is at least 1 for non-negative rate and horizon)

## Why this lemma

Mathlib has `Real.exp_pos`, `Real.exp_zero`, and `Real.exp_le_exp`,
but no named `compound_interest` or `continuous_compounding`
declaration. Pythia exposes the closed-form account-value function
and its boundary / monotonicity properties so the `pythia` tactic
cascade can close fixed-income / discount-factor goals.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.2 (continuous compounding).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Continuously-compounded account value
    `A(P, r, t) = P · exp(r · t)`. -/
noncomputable def compoundContinuous (P r t : ℝ) : ℝ :=
  P * Real.exp (r * t)

/-- **Positivity.** For positive principal, the continuously-compounded
account value is strictly positive at any rate and time horizon. -/
@[stat_lemma]
theorem compoundContinuous_pos {P : ℝ} (hP : 0 < P) (r t : ℝ) :
    0 < compoundContinuous P r t := by
  unfold compoundContinuous
  exact mul_pos hP (Real.exp_pos _)

/-- **Boundary at `t = 0`.** The account value at time zero equals the
principal: `compoundContinuous P r 0 = P`. -/
@[stat_lemma]
theorem compoundContinuous_zero_time (P r : ℝ) :
    compoundContinuous P r 0 = P := by
  unfold compoundContinuous
  simp [mul_zero, Real.exp_zero]

/-- **Compound factor at least 1.** When `r · t ≥ 0`, the compound
factor `exp(r · t)` is at least 1.  Specialises to the everyday
non-negative-rate, non-negative-horizon case. -/
@[stat_lemma]
theorem compoundContinuous_exp_ge_one {r t : ℝ} (h : 0 ≤ r * t) :
    1 ≤ Real.exp (r * t) := by
  exact Real.one_le_exp h

/-- **Monotone in time horizon.** For non-negative principal and
non-negative rate, the account value is monotone non-decreasing in
the time horizon `t`. -/
@[stat_lemma]
theorem compoundContinuous_monotone_t {P r : ℝ} (hP : 0 ≤ P) (hr : 0 ≤ r)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    compoundContinuous P r t₁ ≤ compoundContinuous P r t₂ := by
  unfold compoundContinuous
  apply mul_le_mul_of_nonneg_left _ hP
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hr)

end Pythia.Finance
