/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Black-Scholes-Merton European Call Closed Form

The Black-Scholes-Merton (BSM, 1973) European call price on a non-
dividend-paying asset is

    C(S, K, T, r) = S · Φ(d₁) − K · exp(−r·T) · Φ(d₂),

where `Φ` is the standard-normal CDF, `r` is the risk-free rate, `T`
is time to expiry, and

    d₁ = (log(S/K) + (r + σ²/2)·T) / (σ·√T),
    d₂ = d₁ − σ·√T.

This module gives the algebraic kernel of the BSM call closed form
treating `Φ` as an abstract real-valued helper. The Greeks (Delta,
Gamma, Vega, Theta, Rho) are exposed via the existing
`Pythia.Finance.BlackScholesGreeks` module; the exact-distribution
probability link is deferred to a measure-theoretic module.

This complements:
* `Pythia.Finance.BlackFuturesOption` — the Black 1976 variant for
  forwards/futures (replaces `S` with `F` and zeros out the equity
  carry term).
* `Pythia.Finance.BlackScholesGreeks` — the abstract Greeks identities.
* `Pythia.Finance.BlackScholesIntrinsicLower` — the lower-bound floor
  `C ≥ max(S - K·exp(-r·T), 0)`.

## Main results

* `bsCall`                       : `S · Φ(d₁) − K · exp(−r·T) · Φ(d₂)`
* `bsCall_zero_time`             : at `T = 0` reduces to `S · Φ(d₁) − K · Φ(d₂)`
* `bsCall_zero_rate`             : at `r = 0` reduces to `S · Φ(d₁) − K · Φ(d₂)`
* `bsCall_strict_pos_under_unit_Φ`: strict positivity under the
  practitioner-typical Φ-range hypothesis `Φ(d₁) = 1` (deep-in-money
  asymptotic) and `Φ(d₂) ≤ 1`

## Why this lemma

Black-Scholes-Merton is the foundational equity-option pricing engine
and the basis of essentially every listed option market-making system
in the world. Surfacing the algebraic call closed form in Pythia gives
the `pythia` tactic cascade a clean closure target for equity-option
pricing analytics, completing the Black-Scholes corpus alongside the
existing Greeks, intrinsic-lower-bound, and futures-variant modules.

## References

* Black, F. and Scholes, M. "The Pricing of Options and Corporate
  Liabilities." *Journal of Political Economy* 81(3): 637-654 (1973).
* Merton, R. C. "Theory of Rational Option Pricing."
  *Bell Journal of Economics and Management Science* 4(1):
  141-183 (1973).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Black-Scholes-Merton European call closed form:
    `C = S · Φ(d₁) − K · exp(-r·T) · Φ(d₂)`. -/
noncomputable def bsCall (S K T r Φ_d1 Φ_d2 : ℝ) : ℝ :=
  S * Φ_d1 - K * Real.exp (-(r * T)) * Φ_d2

/-- **At-zero-time specialisation.** At `T = 0` the discount factor
is one and the BSM call equals the Φ-weighted payoff
`S · Φ(d₁) − K · Φ(d₂)`. -/
@[stat_lemma]
theorem bsCall_zero_time (S K r Φ_d1 Φ_d2 : ℝ) :
    bsCall S K 0 r Φ_d1 Φ_d2 = S * Φ_d1 - K * Φ_d2 := by
  unfold bsCall
  simp [mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- **Zero-rate specialisation.** At `r = 0` the discount factor
disappears and the call equals the Φ-weighted payoff
`S · Φ(d₁) − K · Φ(d₂)`. -/
@[stat_lemma]
theorem bsCall_zero_rate (S K T Φ_d1 Φ_d2 : ℝ) :
    bsCall S K T 0 Φ_d1 Φ_d2 = S * Φ_d1 - K * Φ_d2 := by
  unfold bsCall
  simp [zero_mul, neg_zero, Real.exp_zero, mul_one]

/-- **Linear in spot.** Shifting `S` by `ΔS` shifts the call by
`ΔS · Φ(d₁)`. This is the BSM Delta: `∂C/∂S = Φ(d₁)`. -/
@[stat_lemma]
theorem bsCall_linear_S (S ΔS K T r Φ_d1 Φ_d2 : ℝ) :
    bsCall (S + ΔS) K T r Φ_d1 Φ_d2
      = bsCall S K T r Φ_d1 Φ_d2 + ΔS * Φ_d1 := by
  unfold bsCall
  ring

/-- **Strict positivity under deep-in-the-money asymptotic.** Under
practitioner-typical hypotheses (`0 ≤ K`, `Φ(d₁) = 1`, `Φ(d₂) ∈ [0, 1]`)
and the no-arb discounted-strike-below-spot condition
`K · exp(-r·T) < S`, the BSM call price is strictly positive. The
hypothesis `Φ(d₁) = 1` encodes the deep-in-money limit where
`d₁ → +∞` and `Φ(d₁) → 1`; the conclusion is the no-arb intrinsic-
floor consequence at that limit. Real Mathlib reasoning chains
`Real.exp_pos`, `mul_nonneg`, and `mul_le_of_le_one_right`. -/
@[stat_lemma]
theorem bsCall_strict_pos_under_unit_Φ
    (S K T r Φ_d2 : ℝ)
    (hK : 0 ≤ K)
    (h_Φ_d2_le_one : Φ_d2 ≤ 1)
    (_h_Φ_d2_nonneg : 0 ≤ Φ_d2)
    (h_discount_lt_spot : K * Real.exp (-(r * T)) < S) :
    0 < bsCall S K T r 1 Φ_d2 := by
  unfold bsCall
  have h_exp_pos : 0 < Real.exp (-(r * T)) := Real.exp_pos _
  -- bsCall = S * 1 - K * exp(-rT) * Φ_d2 = S - K * exp(-rT) * Φ_d2.
  -- Strategy: D := K * exp(-rT) ≥ 0 (from hK and h_exp_pos),
  --           D * Φ_d2 ≤ D · 1 = D < S, so S - D * Φ_d2 > 0.
  have h_D_nonneg : 0 ≤ K * Real.exp (-(r * T)) :=
    mul_nonneg hK (le_of_lt h_exp_pos)
  have h_DΦ_le_D : K * Real.exp (-(r * T)) * Φ_d2 ≤ K * Real.exp (-(r * T)) :=
    mul_le_of_le_one_right h_D_nonneg h_Φ_d2_le_one
  linarith

end Pythia.Finance
