/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Black 1976 Futures Option Closed Form (forward-price Black-Scholes)

The Black (1976) model prices European options on forward or futures
prices. Unlike the spot-price Black-Scholes formula, the forward
price `F` is already a martingale under the risk-neutral measure (no
carry cost), so the call closed form simplifies to

    Call_F(F, K, T, r) = exp(-r·T) · (F · Φ(d₁) − K · Φ(d₂)),

where `Φ` is the standard-normal CDF, `r` the risk-free rate, `T` the
time to expiry, and

    d₁ = (log(F/K) + (σ²/2)·T) / (σ · √T),    d₂ = d₁ − σ · √T.

The structure is the spot-price Black-Scholes formula with `S` replaced
by `F` and the equity carry term `(r − q)` zeroed. This module gives
the algebraic kernel of the call payoff treating `Φ` as an abstract
real-valued helper (no normality theorem required at this layer); the
exact-distribution probability link is deferred to a measure-theoretic
module.

The Black model is the practitioner-standard pricing engine for:
* Interest-rate caps and floors (each caplet is a Black call on the
  forward LIBOR/SOFR rate)
* European swaptions
* Commodity options
* Equity-index futures options

## Main results

* `blackFuturesCall`                : `exp(-r·T) · (F · Φ(d₁) − K · Φ(d₂))`
* `blackFuturesCall_zero_time`      : at `T = 0` reduces to intrinsic-like payoff
* `blackFuturesCall_zero_rate`      : at `r = 0` the discount disappears
* `blackFuturesCall_linear_F`       : linear shift of `F` translates the call by `exp(-r·T) · ΔF · Φ(d₁)`

## Why this lemma

The Black model is the single most-used option-pricing engine in
fixed-income (caps, floors, swaptions are all priced via Black-on-
forward-LIBOR / Black-on-forward-rate) and in commodity derivatives.
Surfacing the algebraic Black closed form in Pythia gives the `pythia`
tactic cascade a clean closure target for fixed-income / commodity
options analytics.

## References

* Black, F. "The Pricing of Commodity Contracts."
  *Journal of Financial Economics* 3(1-2): 167-179 (1976).
* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §16.6 (Black's model).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Black 1976 futures call closed form:
    `Call_F = exp(-r·T) · (F · Φ(d₁) − K · Φ(d₂))`. -/
noncomputable def blackFuturesCall
    (F K T r Φ_d1 Φ_d2 : ℝ) : ℝ :=
  Real.exp (-(r * T)) * (F * Φ_d1 - K * Φ_d2)

/-- **At-zero-time specialisation.** At `T = 0` the discount factor
is one and the call equals the (Φ-weighted) intrinsic-like payoff
`F · Φ(d₁) − K · Φ(d₂)`. -/
@[stat_lemma]
theorem blackFuturesCall_zero_time (F K r Φ_d1 Φ_d2 : ℝ) :
    blackFuturesCall F K 0 r Φ_d1 Φ_d2 = F * Φ_d1 - K * Φ_d2 := by
  unfold blackFuturesCall
  simp [mul_zero, neg_zero, Real.exp_zero, one_mul]

/-- **Zero-rate specialisation.** At `r = 0` the discount factor
disappears and the call equals the Φ-weighted forward payoff. -/
@[stat_lemma]
theorem blackFuturesCall_zero_rate (F K T Φ_d1 Φ_d2 : ℝ) :
    blackFuturesCall F K T 0 Φ_d1 Φ_d2 = F * Φ_d1 - K * Φ_d2 := by
  unfold blackFuturesCall
  simp [zero_mul, neg_zero, Real.exp_zero, one_mul]

/-- **Linear in forward price.** Shifting `F` by `ΔF` shifts the call
by `exp(-r·T) · ΔF · Φ(d₁)`. This is the abstract Delta for the
Black model: `∂Call/∂F = exp(-r·T) · Φ(d₁)`. -/
@[stat_lemma]
theorem blackFuturesCall_linear_F (F ΔF K T r Φ_d1 Φ_d2 : ℝ) :
    blackFuturesCall (F + ΔF) K T r Φ_d1 Φ_d2
      = blackFuturesCall F K T r Φ_d1 Φ_d2
          + Real.exp (-(r * T)) * (ΔF * Φ_d1) := by
  unfold blackFuturesCall
  ring

end Pythia.Finance
