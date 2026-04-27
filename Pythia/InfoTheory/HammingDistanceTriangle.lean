/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hamming distance on 3-bit binary tuples satisfies the triangle inequality.

Hamming distance on 3-bit binary tuples satisfies the triangle inequality.

## Main results

* `hamming_distance_triangle` — Hamming distance on 3-bit binary tuples satisfies the triangle inequality.

## References

    * Hamming, R.W. Bell System Technical Journal 29(2): 147-160 (1950)
-/
import Mathlib
import Pythia.Tactic.Pythia


namespace Pythia.InfoTheory

/-- Hamming distance on 3-bit Boolean tuples: count of positions where the two tuples differ. -/
def hamming3 : Bool × Bool × Bool → Bool × Bool × Bool → Nat
  | (a0, a1, a2), (b0, b1, b2) =>
      (if a0 = b0 then 0 else 1)
      + (if a1 = b1 then 0 else 1)
      + (if a2 = b2 then 0 else 1)

/-- **Hamming distance triangle inequality (3-bit tuples).** For any
three 3-bit Boolean tuples `a, b, c`, the Hamming distance satisfies
`d(a, c) ≤ d(a, b) + d(b, c)`. Hamming's 1950 metric is the
foundational setting for binary error-correcting codes; this is the
metric-axiom triangle inequality, here over a 512-case finite product
type. The proof closes by exhaustive case analysis: destructure the
three product types into nine independent Boolean components, then
`decide` runs the truth table. -/
@[stat_lemma]
theorem hamming_distance_triangle (a b c : Bool × Bool × Bool) :
    hamming3 a c ≤ hamming3 a b + hamming3 b c := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  obtain ⟨c0, c1, c2⟩ := c
  revert a0 a1 a2 b0 b1 b2 c0 c1 c2
  decide

end Pythia.InfoTheory
