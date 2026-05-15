/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vasicek Zero-Coupon Bond Price (affine term-structure closed form)

Under the Vasicek (1977) short-rate model `dr = a(b − r)dt + σ dW`,
the price at time 0 of a zero-coupon bond maturing at `T` admits the
affine closed form

    P(0, T) = A(T) · exp(−B(T) · r₀),

where

    B(T) = (1 − exp(−a·T)) / a,
    log A(T) = (B(T) − T) · (a²·b − σ²/2) / a² − σ²·B(T)² / (4·a).

This module gives the algebraic kernel of the bond-price closed form
treating `A(T)` and `B(T)` as named real parameters; the
stochastic-integral derivation linking them to `(a, b, σ)` is deferred
to a probability-tier module. The pair `(A, B)` is the standard
"affine term structure" decomposition.

## Main results

* `vasicekBondPrice`             : `A · exp(−B · r₀)`
* `vasicekBondPrice_at_zero_r0`  : at `r₀ = 0` the bond price equals `A`
* `vasicekBondPrice_at_zero_B`   : at `B = 0` the bond price equals `A`
* `vasicekBondPrice_linear_log`  : `log P` is affine in `r₀` with slope `−B`

## Why this lemma

Vasicek's bond-price closed form is the foundational affine-term-
structure identity used by practitioner-standard short-rate model
calibration. Surfacing the algebraic kernel in Pythia gives the
`pythia` tactic cascade a clean closure target for affine term-
structure analytics (Hull-White, G2++, CIR all share the same shape).

## References

* Vasicek, O. "An Equilibrium Characterization of the Term
  Structure." *Journal of Financial Economics* 5(2): 177-188 (1977).
* Duffie, D. and Kan, R. "A Yield-Factor Model of Interest Rates."
  *Mathematical Finance* 6(4): 379-406 (1996).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Vasicek zero-coupon bond price under affine term structure:
    `P(0, T) = A · exp(−B · r₀)`. -/
noncomputable def vasicekBondPrice (A B r₀ : ℝ) : ℝ :=
  A * Real.exp (-(B * r₀))

/-- **At-zero-initial-rate specialisation.** When `r₀ = 0` the bond
price reduces to the affine prefactor `A`. -/
@[stat_lemma]
theorem vasicekBondPrice_at_zero_r0 (A B : ℝ) :
    vasicekBondPrice A B 0 = A := by
  unfold vasicekBondPrice
  simp [mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- **At-zero-B specialisation.** When `B = 0` (instantaneous
maturity in the affine factor) the bond price equals `A`. -/
@[stat_lemma]
theorem vasicekBondPrice_at_zero_B (A r₀ : ℝ) :
    vasicekBondPrice A 0 r₀ = A := by
  unfold vasicekBondPrice
  simp [zero_mul, neg_zero, Real.exp_zero, mul_one]

/-- **Linear-log identity.** For `0 < A`, the log of the Vasicek
bond price is affine in `r₀` with slope `−B`:
    `log P = log A − B · r₀`. This is the linear-Gaussian-rate
core identity used in short-rate model calibration. -/
@[stat_lemma]
theorem vasicekBondPrice_linear_log (A B r₀ : ℝ) (hA : 0 < A) :
    Real.log (vasicekBondPrice A B r₀) = Real.log A - B * r₀ := by
  unfold vasicekBondPrice
  rw [Real.log_mul hA.ne' (Real.exp_pos _).ne']
  rw [Real.log_exp]
  ring

end Pythia.Finance
