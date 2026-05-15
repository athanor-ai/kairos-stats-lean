/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Volatility Smile / Skew

The *implied volatility smile* is the mapping from option moneyness to
the Black-Scholes implied volatility that reproduces the observed option
price.  When moneyness is defined as `m = log(K/S)` (log-strike minus
log-spot), the smile exhibits three canonical features:

1. **ATM level**: at `m = 0` the implied vol equals the at-the-money
   volatility `sigma_atm`.
2. **Smile symmetry** (pure-diffusion / stochastic-vol models with zero
   correlation): `vol(m) = vol(-m)`, i.e. the skew parameter vanishes
   and the surface is symmetric around the ATM point.
3. **Skew**: a non-zero first derivative at `m = 0` breaks the symmetry
   and is the *risk-reversal* (skew) coefficient prominent in FX and
   equity option markets.

For algebraic tractability, we model the implied vol surface as the
quadratic approximation

    vol(m) = sigma_atm + skew * m + smile * m^2,

which is the leading-order Taylor expansion around `m = 0` used by
practitioners for strike interpolation within a single expiry.

## Main results

* `impliedVol`                        : quadratic smile parametrisation
* `impliedVol_atm`                    : `impliedVol sigma_atm skew smile 0 = sigma_atm`
* `impliedVol_symmetric_no_skew`      : when `skew = 0` the surface is symmetric
* `impliedVol_quadratic_form`         : unfolds the definition (ring identity)
* `impliedVol_nonneg_sufficient`      : sufficient condition for non-negative vol
* `impliedVol_mono_smile`             : higher smile coefficient increases vol away from ATM

## Why this module

Implied-vol surface parametrisations are the lingua franca of
derivatives desks.  Surfacing the quadratic smile model in Pythia gives
the `pythia` tactic cascade closure targets for: ATM level checks,
symmetry tests (the zero-skew case is the backbone of SABR/Heston
calibration sanity checks), and monotonicity of vol with respect to
the convexity (smile) parameter (used in butterfly spread pricing
bounds).

## References

* Gatheral, J. "The Volatility Surface." Wiley (2006).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Quadratic implied-volatility smile parametrisation.

Given
- `sigma_atm`: at-the-money implied volatility (the constant term),
- `skew`: first-order moneyness sensitivity (risk-reversal coefficient),
- `smile`: second-order moneyness sensitivity (butterfly / convexity coefficient),
- `m`: log-moneyness `log(K/S)`,

the implied volatility is approximated by the quadratic

    impliedVol sigma_atm skew smile m = sigma_atm + skew * m + smile * m^2.

This is the leading-order Taylor expansion of the smile around the
ATM point, as in Gatheral (2006), Chapter 1. -/
def impliedVol (sigma_atm skew smile m : ℝ) : ℝ :=
  sigma_atm + skew * m + smile * m ^ 2

/-! ## Core lemmas -/

/-- **ATM level.** At zero moneyness the implied vol equals `sigma_atm`. -/
@[stat_lemma]
theorem impliedVol_atm (sigma_atm skew smile : ℝ) :
    impliedVol sigma_atm skew smile 0 = sigma_atm := by
  unfold impliedVol; ring

/-- **Smile symmetry without skew.** When the skew parameter is zero,
the implied vol surface is symmetric around the ATM point:

    impliedVol sigma_atm 0 smile m = impliedVol sigma_atm 0 smile (-m).

This holds because `m^2 = (-m)^2` — a ring identity — and the linear
skew term vanishes. -/
@[stat_lemma]
theorem impliedVol_symmetric_no_skew (sigma_atm smile m : ℝ) :
    impliedVol sigma_atm 0 smile m = impliedVol sigma_atm 0 smile (-m) := by
  unfold impliedVol; ring

/-- **Quadratic form identity.** The definition unfolds to the explicit
quadratic expression.  Provided as a named lemma so the `pythia` tactic
cascade can use it as a rewrite target. -/
@[stat_lemma]
theorem impliedVol_quadratic_form (sigma_atm skew smile m : ℝ) :
    impliedVol sigma_atm skew smile m = sigma_atm + skew * m + smile * m ^ 2 := by
  unfold impliedVol; ring

/-- **Sufficient condition for non-negativity.** If

- `sigma_atm > 0` (positive ATM vol),
- `smile >= 0` (non-negative curvature), and
- `|skew * m| <= sigma_atm + smile * m^2`
  (the skew contribution does not overwhelm the base-plus-curvature floor),

then the implied vol is non-negative. -/
@[stat_lemma]
theorem impliedVol_nonneg_sufficient (sigma_atm skew smile m : ℝ)
    (_ : 0 < sigma_atm)
    (_ : 0 ≤ smile)
    (h_bound : |skew * m| ≤ sigma_atm + smile * m ^ 2) :
    0 ≤ impliedVol sigma_atm skew smile m := by
  unfold impliedVol
  have hab := (abs_le.mp h_bound).1
  linarith

/-- **Monotone in smile.** For any fixed moneyness `m ≠ 0`, increasing
the smile coefficient increases the implied vol:

    smile₁ ≤ smile₂  →  impliedVol sigma_atm skew smile₁ m ≤ impliedVol sigma_atm skew smile₂ m.

The proof uses `mul_le_mul_of_nonneg_right` on the inequality
`smile₁ ≤ smile₂` with the non-negative weight `m^2 ≥ 0`
(by `sq_nonneg`). -/
@[stat_lemma]
theorem impliedVol_mono_smile (sigma_atm skew m : ℝ)
    {smile₁ smile₂ : ℝ} (h : smile₁ ≤ smile₂) (_ : m ≠ 0) :
    impliedVol sigma_atm skew smile₁ m ≤ impliedVol sigma_atm skew smile₂ m := by
  unfold impliedVol
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  have hmono : smile₁ * m ^ 2 ≤ smile₂ * m ^ 2 :=
    mul_le_mul_of_nonneg_right h hm2
  linarith

end Pythia.Finance
