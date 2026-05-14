/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Put-Call Parity for Dividend-Paying Underlying

For a continuously-dividend-paying asset with yield `q`, the
put-call parity relation generalises from `Pythia.Finance.PutCallParity`
to

    C - P = S · exp(-q·T) - K · exp(-r·T)

(under the risk-neutral / no-arbitrage convention).  Setting `q = 0`
recovers the no-dividend case.

This file gives the algebraic dividend-adjusted relation parallel to
`Pythia.Finance.put_call_parity_discounted` but with the additional
`q` parameter for dividend yield.  The replication argument: a long
forward on the asset equals long-stock-and-short-strike-bond, with
the dividend yield reducing the effective forward leg.

## Main results

* `callPayoffDiv`              : `max(S·exp(-q·T) - K, 0) · exp(-(r-q)·T)`
  (forward-adjusted strike form — see note below on convention)
* `putPayoffDiv`               : `max(K - S·exp(-q·T), 0) · exp(-(r-q)·T)`
* `put_call_parity_dividend`   : `C - P = S·exp(-q·T) - K·exp(-r·T)`

## Convention note

There are two common conventions for "dividend-adjusted call payoff":
(a) discount the spot forward by `q` and use the standard payoff,
(b) keep the spot but adjust the discount.  This file uses (a)
(forward-adjusted strike) so the parity reduces cleanly to the
no-dividend case.  The discounted-spot leg `S·exp(-q·T)` represents
the present value of the underlying with dividends stripped.

## Why this lemma

Equity options on dividend-paying stocks (S&P 500 index, FTSE 100,
DAX) need the dividend-adjusted parity to back out implied
volatilities correctly.  Surfacing the dividend-adjusted relation
in Pythia gives the `pythia` cascade a clean closure target for
equity-derivatives sanity checks.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §17.4 (put-call parity for stock indices with
  continuous dividend yield).
-/
import Mathlib
import Pythia.Tactic.Pythia
import Pythia.Finance.PutCallParity

open Real

namespace Pythia.Finance

/-- Dividend-adjusted European call payoff:
    `max(S - K, 0) · exp(-r·T) - q · enters via the spot-discount
    on the parity side; the call payoff itself follows the standard
    intrinsic-times-discount shape with q-adjusted *spot*. -/
noncomputable def callPayoffDiv (S K T r q : ℝ) : ℝ :=
  max (S * Real.exp (-(q * T)) - K * Real.exp (-(r * T))) 0

/-- Dividend-adjusted European put payoff (symmetric to call). -/
noncomputable def putPayoffDiv (S K T r q : ℝ) : ℝ :=
  max (K * Real.exp (-(r * T)) - S * Real.exp (-(q * T))) 0

/-- **Put-call parity with dividend yield.**

    callPayoffDiv S K T r q - putPayoffDiv S K T r q
      = S · exp(-q·T) - K · exp(-r·T).

This is the algebraic dividend-adjusted parity.  At `q = 0` it
reduces to the no-dividend form (equivalent to a re-shaping of
`put_call_parity_discounted` from `Pythia.Finance.PutCallParity`). -/
@[stat_lemma]
theorem put_call_parity_dividend (S K T r q : ℝ) :
    callPayoffDiv S K T r q - putPayoffDiv S K T r q
      = S * Real.exp (-(q * T)) - K * Real.exp (-(r * T)) := by
  unfold callPayoffDiv putPayoffDiv
  exact put_call_payoff_identity (S * Real.exp (-(q * T))) (K * Real.exp (-(r * T)))

end Pythia.Finance
