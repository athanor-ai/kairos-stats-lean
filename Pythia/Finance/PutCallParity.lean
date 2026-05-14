/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Put-Call Parity (algebraic kernel + discounted form)

For a European call with payoff `max(S - K, 0)` and a European put with
payoff `max(K - S, 0)`, the difference of payoffs satisfies the
identity

    max(S - K, 0) - max(K - S, 0) = S - K

for all real `S, K`.  This is the algebraic kernel underlying *put-call
parity*: at expiry, holding a long call and a short put replicates a
forward contract with strike `K` on the underlying.

Discounting both payoffs by the continuous-compounding factor
`exp(-r·T)` gives

    callPayoff S K T r - putPayoff S K T r = (S - K) · exp(-r·T)

where `callPayoff S K T r = max(S - K, 0) · exp(-r·T)` and
`putPayoff S K T r = max(K - S, 0) · exp(-r·T)`.  This is the
spot-form put-call parity used by quant practitioners under the
risk-neutral pricing convention adopted by `Pythia.Economics.RiskNeutralCall`.

## Main results

* `put_call_payoff_identity`   : `max(S-K,0) - max(K-S,0) = S - K`
* `callPayoff`                 : discounted call payoff `max(S-K,0) · exp(-rT)`
* `putPayoff`                  : discounted put payoff  `max(K-S,0) · exp(-rT)`
* `put_call_parity_discounted` : `callPayoff S K T r - putPayoff S K T r = (S - K) · exp(-rT)`

## Why this lemma

Mathlib has `max_sub_max_le_max` and friends, but no named
`put_call_parity` declaration.  Pythia exposes the algebraic kernel
and its discounted form so the `pythia` tactic cascade can close
quant-finance pricing goals without the user reaching for the
underlying real-analysis lemmas directly.

## References

* Stoll, H. R. "The Relationship Between Put and Call Option Prices."
  *Journal of Finance* 24(5): 801-824 (1969).
  (Classical statement and replication argument.)
* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §11.4.
  (Standard quant textbook reference.)
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- **Put-call parity at expiry — algebraic kernel.**

For all real `S` and `K`, the difference between the call payoff
`max(S - K, 0)` and the put payoff `max(K - S, 0)` equals the
forward payoff `S - K`. -/
@[stat_lemma]
theorem put_call_payoff_identity (S K : ℝ) :
    max (S - K) 0 - max (K - S) 0 = S - K := by
  simp only [max_def]
  split_ifs with h1 h2 h3 <;> linarith

/-- The discounted European call payoff `max(S - K, 0) · exp(-r·T)`.

This mirrors the discounting convention of
`Pythia.Economics.RiskNeutralCall.riskNeutralCall`.  Arguments are
unconstrained reals; the meaningful domain is `S, K > 0`, `T ≥ 0`,
and `r` any real (negative rates are permitted, as in post-2008
markets). -/
noncomputable def callPayoff (S K T r : ℝ) : ℝ :=
  max (S - K) 0 * Real.exp (-(r * T))

/-- The discounted European put payoff `max(K - S, 0) · exp(-r·T)`.

Mirrors `callPayoff` with `(S - K)` swapped for `(K - S)` in the
intrinsic-value term. -/
noncomputable def putPayoff (S K T r : ℝ) : ℝ :=
  max (K - S) 0 * Real.exp (-(r * T))

/-- **Put-call parity (discounted, spot-form).**

For any `S, K, T, r : ℝ`,

    callPayoff S K T r - putPayoff S K T r = (S - K) · exp(-r·T).

This is the standard quant-finance put-call parity relation in the
risk-neutral pricing convention.  At `T = 0` it specialises to the
algebraic kernel `put_call_payoff_identity` (since
`exp(-r·0) = 1`). -/
@[stat_lemma]
theorem put_call_parity_discounted (S K T r : ℝ) :
    callPayoff S K T r - putPayoff S K T r = (S - K) * Real.exp (-(r * T)) := by
  unfold callPayoff putPayoff
  rw [← sub_mul, put_call_payoff_identity]

end Pythia.Finance
