/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# European Call Price Upper Bound

Under no-arbitrage, a European call option on a non-negative underlying
satisfies the upper bound

    callPayoff S K T r ≤ S

whenever the strike `K ≥ 0`, time to expiry `T ≥ 0`, and interest
rate `r ≥ 0`.  The economic content: a call option cannot be worth
more than the underlying asset itself (one can always replicate the
"buy the stock" payoff dominated by the call exercise).

## Main results

* `callPayoff_le_spot` : `0 ≤ S → 0 ≤ K → 0 ≤ T → 0 ≤ r → callPayoff S K T r ≤ S`

## Why this lemma

Mathlib has `max_le`, `Real.exp_le_one`, `mul_le_one`, but no named
`call_price_upper_bound` declaration.  Pythia surfaces this no-arbitrage
upper bound so the `pythia` tactic cascade can close option-bound
sanity checks (the bedrock of practitioner arbitrage tables).

Algebraically the bound decomposes into `max (S - K) 0 ≤ S` (under
`0 ≤ K`) and `Real.exp (-(r·T)) ≤ 1` (under `0 ≤ r·T`); composing
the two factors yields the bound.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §11.2 (option-price upper bounds — `c ≤ S`).
-/
import Mathlib
import Pythia.Finance.Options.PutCallParity
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- **Call option ≤ underlying.** Under no-arbitrage, for non-negative
spot / strike / horizon / rate, the discounted European call payoff
is bounded above by the spot price `S`. -/
@[stat_lemma]
theorem callPayoff_le_spot
    {S K T r : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) (hT : 0 ≤ T) (hr : 0 ≤ r) :
    callPayoff S K T r ≤ S := by
  unfold callPayoff
  have h_max_le : max (S - K) 0 ≤ S := max_le (by linarith) hS
  have h_rT_nonneg : 0 ≤ r * T := mul_nonneg hr hT
  have h_exp_le : Real.exp (-(r * T)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_max_nonneg : 0 ≤ max (S - K) 0 := le_max_right _ _
  calc max (S - K) 0 * Real.exp (-(r * T))
      ≤ max (S - K) 0 * 1 :=
        mul_le_mul_of_nonneg_left h_exp_le h_max_nonneg
    _ = max (S - K) 0 := mul_one _
    _ ≤ S := h_max_le

end Pythia.Finance
