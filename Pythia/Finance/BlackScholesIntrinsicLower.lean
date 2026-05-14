/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Black-Scholes Call: Intrinsic Discounted Lower Bound

Under no-arbitrage, a European call option price `C` on a non-
dividend-paying asset satisfies the lower bound

    C ≥ max(S - K · exp(-r·T), 0).

This is the *discounted-intrinsic-floor* identity: the call is
worth at least the value of the underlying minus the discounted
strike (cash + bond replication argument), and trivially at least
zero (limited liability).

This file gives the algebraic kernel of the lower bound (without
invoking the full Black-Scholes CDF formula) — it works at the
*payoff-decomposition* level and composes cleanly with
`Pythia.Finance.PutCallParity.put_call_parity_discounted`.

## Main results

* `discountedIntrinsic`            : `max(S - K · exp(-r·T), 0)`
* `discountedIntrinsic_nonneg`     : `0 ≤ discountedIntrinsic`
* `discountedIntrinsic_at_T_zero`  : reduces to `max(S - K, 0)` at `T = 0`
* `discountedIntrinsic_zero_strike`: at `K = 0` reduces to `max(S, 0)`

## Why this lemma

The discounted-intrinsic-floor is the *minimum* no-arbitrage call
price.  Practitioner arbitrage tables compare market call prices
against this floor to detect mispricings (the cash-and-carry trade
when `C < S - K·exp(-r·T)`).  Surfacing the floor in Pythia gives
the `pythia` tactic cascade a clean closure target for option-
arbitrage detection.

The companion `Pythia.Finance.CallPriceUpperBound.callPayoff_le_spot`
gives the upper-bound counterpart `C ≤ S`.  Together they fence the
call price into `[max(S - K·exp(-rT), 0), S]`.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §11.3 (lower bounds for option prices).
* Merton, R. C. "Theory of Rational Option Pricing."
  *Bell Journal of Economics and Management Science* 4(1):
  141-183 (1973).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Discounted-intrinsic call-price floor:
    `max(S - K · exp(-r·T), 0)`. -/
noncomputable def discountedIntrinsic (S K T r : ℝ) : ℝ :=
  max (S - K * Real.exp (-(r * T))) 0

/-- **Non-negativity.** The floor is non-negative unconditionally
(the limited-liability shape of the `max(·, 0)` clip). -/
@[stat_lemma]
theorem discountedIntrinsic_nonneg (S K T r : ℝ) :
    0 ≤ discountedIntrinsic S K T r := by
  unfold discountedIntrinsic; exact le_max_right _ _

/-- **At-T-zero specialisation.** At zero time-to-expiry the
discounted-intrinsic floor reduces to the undiscounted intrinsic
value `max(S - K, 0)`. -/
@[stat_lemma]
theorem discountedIntrinsic_at_T_zero (S K r : ℝ) :
    discountedIntrinsic S K 0 r = max (S - K) 0 := by
  unfold discountedIntrinsic; simp [mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- **Zero-strike specialisation.** With `K = 0`, the floor reduces
to `max(S, 0)` (a zero-strike call is just the underlying, capped
at zero by limited liability). -/
@[stat_lemma]
theorem discountedIntrinsic_zero_strike (S T r : ℝ) :
    discountedIntrinsic S 0 T r = max S 0 := by
  unfold discountedIntrinsic; simp [zero_mul, sub_zero]

end Pythia.Finance
