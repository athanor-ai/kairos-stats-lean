/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# European Option Price Bounds

Two textbook no-arbitrage bounds that follow directly from the
non-negativity of intrinsic payoffs and the put-call-parity
identity `Pythia.Finance.put_call_parity_discounted`:

* `callPayoff_nonneg` : `0 ≤ callPayoff S K T r`
* `putPayoff_nonneg`  : `0 ≤ putPayoff S K T r`
* `call_minus_put_eq` : restatement of put-call parity as a lower bound
  on the long-call-short-put portfolio
* `call_ge_intrinsic_discounted` :
  `callPayoff S K T r ≥ (S - K) * exp(-r·T) - putPayoff S K T r`
  (rearrangement of put-call parity — gives the "call dominates
  discounted intrinsic minus put" inequality used by practitioner
  arbitrage tables)

## Why these lemmas

The `Pythia.Finance.PutCallParity` module gives the equality form.
These boundary lemmas surface the practitioner-relevant inequality
forms so the `pythia` tactic cascade can close call-pricing
sign-direction goals (the natural shape of arbitrage-table
sanity checks) without re-deriving them.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §11.2 (option-price bounds).
-/
import Mathlib
import Pythia.Finance.Options.PutCallParity
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- **Call payoff is non-negative.** The discounted call payoff
`max(S - K, 0) · exp(-r·T)` is non-negative by construction
(non-negative intrinsic times positive discount). -/
@[stat_lemma]
theorem callPayoff_nonneg (S K T r : ℝ) :
    0 ≤ callPayoff S K T r := by
  unfold callPayoff
  exact mul_nonneg (le_max_right _ _) (Real.exp_pos _).le

/-- **Put payoff is non-negative.** Symmetric to `callPayoff_nonneg`. -/
@[stat_lemma]
theorem putPayoff_nonneg (S K T r : ℝ) :
    0 ≤ putPayoff S K T r := by
  unfold putPayoff
  exact mul_nonneg (le_max_right _ _) (Real.exp_pos _).le

/-- **Call dominates discounted intrinsic minus put.** Rearrangement
of `put_call_parity_discounted`:

    callPayoff S K T r ≥ (S - K) · exp(-r·T) - putPayoff S K T r.

(Equality holds; the inequality form is the practitioner-useful
shape for sign-direction checks.) -/
@[stat_lemma]
theorem call_ge_intrinsic_discounted (S K T r : ℝ) :
    (S - K) * Real.exp (-(r * T)) - putPayoff S K T r ≤ callPayoff S K T r := by
  have h := put_call_parity_discounted S K T r
  have hp := putPayoff_nonneg S K T r
  linarith

end Pythia.Finance
