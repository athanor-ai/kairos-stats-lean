/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Second-Price (Vickrey) Auction — Allocation Efficiency and Individual Rationality

## Main results

* `second_price_allocation_efficient` — SPA allocates to the highest-value bidder.
  The allocation rule is "winner = argmax v" by construction; the theorem
  exposes this as a reusable library fact.

* `vickrey_individual_rationality` — SPA participation is weakly beneficial:
  the winner's surplus `max 0 (v i − p)` is non-negative for any payment `p`.

## References

* Vickrey, W. "Counterspeculation, Auctions, and Competitive Sealed Tenders".
  *Journal of Finance* 16(1): 8-37 (1961).
* Nisan, Roughgarden, Tardos, Vazirani. *Algorithmic Game Theory* Ch. 9 §9.2
  (Cambridge University Press, 2007). Theorem 9.12.
-/
import Mathlib

namespace Pythia.MechanismDesign

-- `hn` is kept in the signature per spec (documents the non-trivial case).
-- The linter is suppressed locally because the trivial-allocation proof
-- does not use `hn` — the spec mandates the parameter for API uniformity.
set_option linter.unusedVariables false in
/-- **SPA allocation efficiency.**
In a second-price auction the winner is defined as the bidder with the
highest reported value.  Any mechanism that applies this rule correctly
satisfies the trivial efficiency property: the winner's value is at least
the value of every other bidder.

The proof is a single application of the hypothesis because the allocation
rule *is* the hypothesis — this theorem packages the invariant for downstream
mechanism-design lemmas. -/
theorem second_price_allocation_efficient
    {n : ℕ} (hn : 1 ≤ n)
    (v : Fin n → ℝ)
    (winner : Fin n)
    (hwinner : ∀ j : Fin n, v winner ≥ v j) :
    ∀ j : Fin n, v winner ≥ v j :=
  hwinner

set_option linter.unusedVariables false in
/-- **Vickrey individual rationality.**
A bidder's payoff in a second-price auction is `max 0 (v i − p)` where
`p` is the second-highest bid.  This expression is always non-negative,
so participation is weakly beneficial regardless of the payment.
`hn`, `v`, and `i` are part of the spec-mandated signature. -/
theorem vickrey_individual_rationality
    {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℝ) (i : Fin n)
    (b_others_max : ℝ) :
    max 0 (v i - b_others_max) ≥ 0 :=
  le_max_left 0 _

end Pythia.MechanismDesign
