/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cox-Ross-Rubinstein One-Step Binomial Option Pricing

The Cox-Ross-Rubinstein (CRR 1979) discrete-time option-pricing model
values a derivative at the start of a one-period binomial tree as the
discounted risk-neutral expectation:

    V₀ = exp(-r·Δt) · (q · V_u + (1 − q) · V_d),

where `V_u`, `V_d` are the option's terminal payoffs in the up/down
states, and `q` is the *risk-neutral probability* of the up state:

    q = (exp(r·Δt) − d) / (u − d),

with `u`, `d` the gross up/down moves of the underlying.

This module gives the algebraic kernel `crrStepPrice` (discounted
risk-neutral expectation) and `crrRiskNeutralProb` (the `q` formula),
plus their interaction identities.

## Main results

* `crrStepPrice`                : `exp(-r·Δt) · (q · V_u + (1 − q) · V_d)`
* `crrRiskNeutralProb`          : `(exp(r·Δt) − d) / (u − d)`
* `crrStepPrice_equal_payoffs`  : `V_u = V_d = V` ⇒ price = `exp(-r·Δt) · V`
* `crrStepPrice_zero_rate`      : at `r = 0` price = `q·V_u + (1 − q)·V_d`
* `crrStepPrice_linear_payoff`  : linear in the payoff pair (V_u, V_d)
* `crrRiskNeutralProb_zero_rate`: at `r = 0` reduces to `(1 − d)/(u − d)`

## Why this lemma

The CRR binomial tree is the *discrete-time* counterpart to the
Black-Scholes PDE — every introductory and practitioner reference on
option pricing (Hull, Wilmott, Shreve) builds from it.  Surfacing the
CRR step identity in Pythia gives the `pythia` tactic cascade a clean
closure target for discrete-time-option-pricing analytics, including
American-option dynamic-programming backward induction.

## References

* Cox, J. C., Ross, S. A., and Rubinstein, M.
  "Option Pricing: A Simplified Approach."
  *Journal of Financial Economics* 7(3): 229-263 (1979).
* Shreve, S. E. *Stochastic Calculus for Finance I: The Binomial
  Asset Pricing Model.* Springer (2004), Ch. 1.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- CRR one-step option price: discounted risk-neutral expectation. -/
noncomputable def crrStepPrice (r Δt q Vu Vd : ℝ) : ℝ :=
  Real.exp (-(r * Δt)) * (q * Vu + (1 - q) * Vd)

/-- CRR one-step risk-neutral up-probability:
    `q = (exp(r·Δt) − d) / (u − d)`. -/
noncomputable def crrRiskNeutralProb (r Δt u d : ℝ) : ℝ :=
  (Real.exp (r * Δt) - d) / (u - d)

/-- **Equal-payoff specialisation.** When the up and down payoffs
coincide (`V_u = V_d = V`) the CRR price reduces to the simple
discount factor times the payoff. -/
@[stat_lemma]
theorem crrStepPrice_equal_payoffs (r Δt q V : ℝ) :
    crrStepPrice r Δt q V V = Real.exp (-(r * Δt)) * V := by
  unfold crrStepPrice
  ring

/-- **Zero-rate specialisation.** At zero interest rate the
discount factor is one and the CRR price reduces to the risk-neutral
expectation `q·V_u + (1 − q)·V_d`. -/
@[stat_lemma]
theorem crrStepPrice_zero_rate (Δt q Vu Vd : ℝ) :
    crrStepPrice 0 Δt q Vu Vd = q * Vu + (1 - q) * Vd := by
  unfold crrStepPrice
  simp [zero_mul, neg_zero, Real.exp_zero, one_mul]

/-- **Linearity in payoff pair.** Scaling both terminal payoffs by
`α` scales the CRR price by `α`. -/
@[stat_lemma]
theorem crrStepPrice_linear_payoff (r Δt q α Vu Vd : ℝ) :
    crrStepPrice r Δt q (α * Vu) (α * Vd)
      = α * crrStepPrice r Δt q Vu Vd := by
  unfold crrStepPrice
  ring

/-- **Zero-rate risk-neutral probability.** At `r = 0` the
risk-neutral probability reduces to `(1 − d)/(u − d)` (no discount
correction needed). -/
@[stat_lemma]
theorem crrRiskNeutralProb_zero_rate (Δt u d : ℝ) :
    crrRiskNeutralProb 0 Δt u d = (1 - d) / (u - d) := by
  unfold crrRiskNeutralProb
  simp [zero_mul, Real.exp_zero]

end Pythia.Finance
