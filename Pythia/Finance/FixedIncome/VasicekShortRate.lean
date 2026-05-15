/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vasicek Short-Rate Model (mean-reverting Gaussian short rate)

The Vasicek (1977) short-rate model specifies the instantaneous risk-
free rate `r_t` as the solution to the mean-reverting SDE

    dr_t = a · (b − r_t) · dt + σ · dW_t,

where `a > 0` is the mean-reversion speed, `b` is the long-run mean,
`σ` is the instantaneous volatility, and `W_t` is a Brownian motion.
The closed-form expectation of `r_t` given `r_0` is

    E[r_t | r_0] = b + (r_0 − b) · exp(−a · t),

which decays exponentially from `r_0` toward the long-run mean `b`.

This module gives the algebraic kernel of the conditional-mean
closed form (the stochastic-integral / variance link is deferred to
a probability-tier module). The structure mirrors
`Pythia.Finance.OrnsteinUhlenbeck` but with the Vasicek-specific
parameter convention `(a, b, σ)` used in interest-rate practice.

## Main results

* `vasicekMean`              : `b + (r₀ − b) · exp(−a·t)`
* `vasicekMean_at_zero_time` : at `t = 0` the mean equals `r₀`
* `vasicekMean_at_long_run`  : at `r₀ = b` the mean is constant at `b`
* `vasicekMean_linear_r0`    : linear shift in `r₀` translates the mean by `Δr · exp(−a·t)`

## Why this lemma

Vasicek is the foundational mean-reverting short-rate model and the
ancestor of every Gaussian short-rate model (Hull-White, G2++,
multi-factor extensions). Its closed-form expectation is the input
to bond-pricing PDE solutions, swaption pricing, and the canonical
calibration target for short-rate model fitting. Surfacing the
algebraic Vasicek closed form in Pythia gives the `pythia` tactic
cascade a clean closure target for short-rate analytics.

## References

* Vasicek, O. "An Equilibrium Characterization of the Term
  Structure." *Journal of Financial Economics* 5(2): 177-188 (1977).
* Brigo, D. and Mercurio, F. *Interest Rate Models: Theory and
  Practice*, 2nd ed. Springer (2006), Ch. 3.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Vasicek short-rate conditional mean: `b + (r₀ − b) · exp(−a·t)`. -/
noncomputable def vasicekMean (r₀ a b t : ℝ) : ℝ :=
  b + (r₀ - b) * Real.exp (-(a * t))

/-- **At-zero-time specialisation.** At `t = 0` the conditional
mean equals the initial rate `r₀` (no decay has occurred yet). -/
@[stat_lemma]
theorem vasicekMean_at_zero_time (r₀ a b : ℝ) :
    vasicekMean r₀ a b 0 = r₀ := by
  unfold vasicekMean
  simp [mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- **Long-run-mean specialisation.** When the initial rate equals
the long-run mean (`r₀ = b`), the Vasicek conditional mean is
constant at `b` for all `t` (no decay applies because there's no
distance to close). -/
@[stat_lemma]
theorem vasicekMean_at_long_run (a b t : ℝ) :
    vasicekMean b a b t = b := by
  unfold vasicekMean
  simp [sub_self, zero_mul, add_zero]

/-- **Linear in initial rate.** Shifting `r₀` by `Δr` shifts the
conditional mean by `Δr · exp(−a·t)`, reflecting the exponential-
decay weight on the initial-rate contribution. -/
@[stat_lemma]
theorem vasicekMean_linear_r0 (r₀ Δr a b t : ℝ) :
    vasicekMean (r₀ + Δr) a b t
      = vasicekMean r₀ a b t + Δr * Real.exp (-(a * t)) := by
  unfold vasicekMean
  ring

end Pythia.Finance
