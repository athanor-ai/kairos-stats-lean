/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cointegration Residual (algebraic kernel)

For two price-series `y, x : ℝ` and cointegration coefficient `β : ℝ`,
the *cointegration residual* is the linear combination

    r(y, x, β) = y - β · x.

In the Engle-Granger (1987) framework, when `x` and `y` are I(1)
(integrated-of-order-1) and cointegrated, the residual `r` is I(0)
(stationary, mean-reverting).  This file gives the algebraic kernel
identities of the residual — linearity in each argument, boundary
cases, and the spread `β = 1` reduction.

The stochastic-process / unit-root link (that the residual is
*actually* stationary under cointegration) is deferred to a
probability-tier module; here we surface the *algebraic backbone*
that practitioner pairs-trading rests on.

## Main results

* `cointegrationResidual`               : `y - β · x`
* `cointegrationResidual_zero_beta`     : `r(y, x, 0) = y`
* `cointegrationResidual_spread`        : `r(y, x, 1) = y - x` (spread shape)
* `cointegrationResidual_linear_in_y`   : linear in `y` (additive shift)
* `cointegrationResidual_scaling`       : scaling-equivariance under `α·(y,x)`

## Why this lemma

Cointegration is the backbone of pairs trading, statistical arbitrage,
and basis-spread modelling.  Practitioners pick `β` by least-squares
regression, then trade the residual on the hypothesis that it
mean-reverts.  Surfacing the algebraic residual identities in Pythia
gives the `pythia` tactic cascade a clean closure target for
stat-arb sign-direction sanity checks.

## References

* Engle, R. F. and Granger, C. W. J.
  "Co-integration and Error Correction: Representation, Estimation,
   and Testing." *Econometrica* 55(2): 251-276 (1987).
* Vidyamurthy, G. *Pairs Trading: Quantitative Methods and Analysis.*
  Wiley (2004).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Cointegration residual `r(y, x, β) = y - β · x`. -/
noncomputable def cointegrationResidual (y x β : ℝ) : ℝ :=
  y - β * x

/-- **Zero coefficient reduces to `y`.** With `β = 0`, the residual
trivially equals `y` (no cointegration correction). -/
@[stat_lemma]
theorem cointegrationResidual_zero_beta (y x : ℝ) :
    cointegrationResidual y x 0 = y := by
  unfold cointegrationResidual; ring

/-- **Unit-coefficient gives the spread.** With `β = 1`, the residual
reduces to the classical spread `y - x` (basis trade). -/
@[stat_lemma]
theorem cointegrationResidual_spread (y x : ℝ) :
    cointegrationResidual y x 1 = y - x := by
  unfold cointegrationResidual; ring

/-- **Linear in `y` under additive shift.** Adding `c` to `y` shifts
the residual by `c`. -/
@[stat_lemma]
theorem cointegrationResidual_linear_in_y (y x β c : ℝ) :
    cointegrationResidual (y + c) x β = cointegrationResidual y x β + c := by
  unfold cointegrationResidual; ring

/-- **Scaling-equivariance.** Rescaling both `y` and `x` by `α` (with
`β` held fixed) rescales the residual by the same `α`. -/
@[stat_lemma]
theorem cointegrationResidual_scaling (α y x β : ℝ) :
    cointegrationResidual (α * y) (α * x) β = α * cointegrationResidual y x β := by
  unfold cointegrationResidual; ring

end Pythia.Finance
