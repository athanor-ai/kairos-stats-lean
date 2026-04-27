/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk-Neutral European Call Option Non-Negativity

The risk-neutral price of a European call option is

    C(S, K, T, r) = max(S - K, 0) * exp(-r * T)

where S is the current stock price, K is the strike price, T >= 0 is
time to expiry, and r is the risk-free rate.  The intrinsic value
`max(S - K, 0)` is non-negative by definition (the option holder
exercises only when it is profitable), and discounting by `exp(-r * T)`
preserves sign because the exponential function is strictly positive for
all real exponents.

## Main results

* `riskNeutralCall`             : the call-price function `max(S-K,0) * exp(-rT)`
* `risk_neutral_call_nonneg`    : `C(S, K, T, r) >= 0` for any S, K, r and T >= 0

## Why this lemma

Mathlib has `Real.exp_pos` and `le_max_right` but no named
`black_scholes` or `option_price` declaration. Pythia exposes the
risk-neutral call price and its non-negativity so the `pythia` tactic
cascade can close option-pricing goals without the user reaching for
the underlying real-analysis lemmas directly.

The companion empirical layer (`tools/sim/economics_risk_neutral_call.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation harness
to confirm the bound holds across in-the-money (S > K), at-the-money
(S = K), out-of-the-money (S < K), and multi-year horizon parameter
ranges.

## References

* Cox, J. C., Ross, S. A., and Rubinstein, M.
  "Option Pricing: A Simplified Approach."
  *Journal of Financial Economics* 7(3): 229-263 (1979).
  (Risk-neutral pricing framework.)
* Black, F. and Scholes, M.
  "The Pricing of Options and Corporate Liabilities."
  *Journal of Political Economy* 81(3): 637-654 (1973).
  (Closed-form option price via no-arbitrage and risk-neutral valuation.)
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Economics

/-- The risk-neutral European call option price
    `C(S, K, T, r) = max(S - K, 0) * exp(-r * T)`.
The arguments are unconstrained reals; the meaningful domain is
`S, K > 0`, `T >= 0`, and `r` any real (including negative, as seen
in post-2008 markets), but the non-negativity result holds for all
real inputs. -/
noncomputable def riskNeutralCall (S K T r : ℝ) : ℝ :=
  max (S - K) 0 * Real.exp (-(r * T))

/-- **Call option non-negativity.** For any stock price `S`, strike
`K`, time to expiry `T`, and risk-free rate `r`, the risk-neutral
European call price is non-negative. The intrinsic value `max(S-K,0)`
is non-negative, and multiplying by the strictly-positive discount
factor `exp(-rT)` preserves the sign. -/
@[stat_lemma]
theorem risk_neutral_call_nonneg (S K T r : ℝ) :
    0 ≤ riskNeutralCall S K T r := by
  unfold riskNeutralCall
  exact mul_nonneg (le_max_right _ _) (Real.exp_pos _).le

end Pythia.Economics
