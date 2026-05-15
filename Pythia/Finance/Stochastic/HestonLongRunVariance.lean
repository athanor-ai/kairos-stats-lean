/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heston Model Long-Run Variance (mean-reverting variance level)

The Heston (1993) stochastic-volatility model couples a price process
to a stochastic variance `v_t` that follows a Cox-Ingersoll-Ross
(square-root) mean-reverting SDE

    dv_t = κ · (θ − v_t) · dt + σ_v · sqrt(v_t) · dW_t.

The conditional expectation of `v_t` given `v_0` admits the closed
form

    E[v_t | v_0] = θ + (v_0 − θ) · exp(−κ · t),

which decays exponentially from `v_0` toward the long-run variance
level `θ`. The structure parallels the Vasicek short-rate conditional
mean (same exponential-decay-toward-long-run shape) and the Ornstein-
Uhlenbeck mean. This module gives the algebraic kernel; the
stochastic-integral / non-central chi-squared variance link is
deferred to a probability-tier module.

## Main results

* `hestonVarianceMean`              : `θ + (v₀ − θ) · exp(−κ·t)`
* `hestonVarianceMean_at_zero_time` : at `t = 0` the mean equals `v₀`
* `hestonVarianceMean_at_long_run`  : at `v₀ = θ` the mean is constant at `θ`
* `hestonVarianceMean_linear_v0`    : linear shift in `v₀` translates the mean by `Δv · exp(−κ·t)`

## Why this lemma

Heston is the practitioner-standard stochastic-volatility model used
in equity-derivatives pricing across exchanges (CBOE VIX models,
listed-equity-option market-makers) and in fixed-income volatility
modelling (caps, swaptions). Surfacing the algebraic kernel of the
variance-mean dynamics in Pythia gives the `pythia` tactic cascade a
clean closure target for Heston-calibration analytics.

## References

* Heston, S. L. "A Closed-Form Solution for Options with Stochastic
  Volatility with Applications to Bond and Currency Options."
  *Review of Financial Studies* 6(2): 327-343 (1993).
* Gatheral, J. *The Volatility Surface: A Practitioner's Guide.*
  Wiley (2006), Ch. 3.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Heston variance conditional mean: `θ + (v₀ − θ) · exp(−κ·t)`. -/
noncomputable def hestonVarianceMean (v₀ κ θ t : ℝ) : ℝ :=
  θ + (v₀ - θ) * Real.exp (-(κ * t))

/-- **At-zero-time specialisation.** At `t = 0` the conditional
variance mean equals the initial variance `v₀`. -/
@[stat_lemma]
theorem hestonVarianceMean_at_zero_time (v₀ κ θ : ℝ) :
    hestonVarianceMean v₀ κ θ 0 = v₀ := by
  unfold hestonVarianceMean
  simp [mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- **Long-run-variance specialisation.** When the initial variance
equals the long-run level (`v₀ = θ`), the Heston conditional
variance mean is constant at `θ` for all `t`. -/
@[stat_lemma]
theorem hestonVarianceMean_at_long_run (κ θ t : ℝ) :
    hestonVarianceMean θ κ θ t = θ := by
  unfold hestonVarianceMean
  simp [sub_self, zero_mul, add_zero]

/-- **Linear in initial variance.** Shifting `v₀` by `Δv` shifts the
conditional variance mean by `Δv · exp(−κ·t)`. -/
@[stat_lemma]
theorem hestonVarianceMean_linear_v0 (v₀ Δv κ θ t : ℝ) :
    hestonVarianceMean (v₀ + Δv) κ θ t
      = hestonVarianceMean v₀ κ θ t + Δv * Real.exp (-(κ * t)) := by
  unfold hestonVarianceMean
  ring

end Pythia.Finance
