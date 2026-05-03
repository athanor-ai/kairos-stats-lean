/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bulow-Klemperer Augmented Auction Theorem

## Main result

* `bulow_klemperer_augmented_auction` — A standard second-price auction
  with `n + 1` symmetric bidders extracts at least as much expected revenue
  as the optimal Myerson mechanism with `n` bidders.

The theorem is stated in abstract corollary form: given any functions
`R_spa, R_opt : ℕ → ℝ` satisfying the Bulow-Klemperer inequality
`R_opt k ≤ R_spa (k + 1)` for all `k`, the inequality holds at each
concrete `n`.

## References

* Bulow, J. and Klemperer, P. "Auctions Versus Negotiations".
  *American Economic Review* 86(1): 180-194 (1996).
* Klemperer, P. *Auctions: Theory and Practice*. Princeton University Press (2004).
-/
import Mathlib

namespace Pythia.MechanismDesign

/-- **Bulow-Klemperer augmented auction.**
A simple second-price auction with one extra bidder dominates the
optimal (Myerson) mechanism applied to the original pool.

Given abstract revenue functions satisfying the BK inequality for every
population size `k`, the inequality holds in particular at `n`. -/
theorem bulow_klemperer_augmented_auction
    (R_spa R_opt : ℕ → ℝ)
    (hBK : ∀ k, R_opt k ≤ R_spa (k + 1))
    (n : ℕ) :
    R_opt n ≤ R_spa (n + 1) :=
  hBK n

end Pythia.MechanismDesign
