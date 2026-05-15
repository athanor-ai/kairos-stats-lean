/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Forward Rate Parity (term-structure no-arbitrage identity)

Under continuous compounding and a no-arbitrage term structure, the
zero-coupon yields `y₁` (maturity `T₁`) and `y₂` (maturity `T₂ > T₁`)
and the *forward rate* `f` for the interval `[T₁, T₂]` satisfy

    exp(y₂ · T₂)  =  exp(y₁ · T₁) · exp(f · (T₂ - T₁)).

Equivalently, in log-form,

    y₂ · T₂  =  y₁ · T₁ + f · (T₂ - T₁),

so the forward rate is the affine combination

    f  =  (y₂ · T₂  -  y₁ · T₁) / (T₂ - T₁).

This is the algebraic backbone of bootstrapping the forward-rate
curve from observed zero-coupon yields — the textbook fixed-income
term-structure identity.

## Main results

* `forwardRate`                    : `(y₂·T₂ - y₁·T₁) / (T₂ - T₁)`
* `forwardRateExp_consistent`      : `exp(y₂·T₂) = exp(y₁·T₁) · exp(f·(T₂-T₁))`
  where `f = forwardRate y₁ y₂ T₁ T₂`
* `forwardRate_at_flat_curve`      : `y₁ = y₂` → `f = y₂` (flat curve)
* `forwardRate_zero_short_horizon` : `T₁ = 0` reduces to `f = y₂` (forward equals long yield)

## Why this lemma

Forward rates are the building blocks of yield-curve modelling,
swap pricing, and fixed-income relative-value trading.  The
forward-rate-parity identity is the no-arbitrage glue between
yields at different maturities.  Surfacing the algebraic identity
in Pythia gives the `pythia` tactic cascade a clean closure target
for term-structure bootstrap sanity checks.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.8 (forward rates and the yield curve).
* Heath, D., Jarrow, R., and Morton, A. "Bond Pricing and the Term
  Structure of Interest Rates: A New Methodology for Contingent
  Claims Valuation." *Econometrica* 60(1): 77-105 (1992).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Forward rate for the interval `[T₁, T₂]` from zero-coupon yields
`y₁, y₂` at maturities `T₁ < T₂`:
    `f = (y₂·T₂ - y₁·T₁) / (T₂ - T₁)`. -/
noncomputable def forwardRate (y₁ y₂ T₁ T₂ : ℝ) : ℝ :=
  (y₂ * T₂ - y₁ * T₁) / (T₂ - T₁)

/-- **Flat-curve specialisation.** When the yield curve is flat
(`y₁ = y₂ = y`), the forward rate equals the common yield. -/
@[stat_lemma]
theorem forwardRate_at_flat_curve {y T₁ T₂ : ℝ} (hT : T₁ ≠ T₂) :
    forwardRate y y T₁ T₂ = y := by
  unfold forwardRate
  have hT' : T₂ - T₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hT)
  field_simp

/-- **Zero short-horizon specialisation.** When `T₁ = 0` (forward
starts immediately), the forward rate equals the long-maturity
yield `y₂`. -/
@[stat_lemma]
theorem forwardRate_zero_short_horizon {y₁ y₂ T₂ : ℝ} (hT : T₂ ≠ 0) :
    forwardRate y₁ y₂ 0 T₂ = y₂ := by
  unfold forwardRate
  simp [hT]

/-- **No-arbitrage consistency (exp form).** The forward rate
satisfies the multiplicative no-arbitrage identity

    exp(y₂ · T₂) = exp(y₁ · T₁) · exp(f · (T₂ - T₁)),

where `f = forwardRate y₁ y₂ T₁ T₂`.  This is the bootstrap
identity: the two-period discount factor decomposes into the
short-period discount factor times the forward-period discount
factor. -/
@[stat_lemma]
theorem forwardRateExp_consistent {y₁ y₂ T₁ T₂ : ℝ} (hT : T₁ ≠ T₂) :
    Real.exp (y₂ * T₂)
      = Real.exp (y₁ * T₁) * Real.exp (forwardRate y₁ y₂ T₁ T₂ * (T₂ - T₁)) := by
  unfold forwardRate
  have hT' : T₂ - T₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hT)
  rw [div_mul_cancel₀ _ hT']
  rw [← Real.exp_add]
  congr 1
  ring

end Pythia.Finance
