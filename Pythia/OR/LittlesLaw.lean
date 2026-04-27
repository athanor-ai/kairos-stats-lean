/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Little's Law Positivity

In a stable queueing system, Little's Law states L = lambda * W, where L is
the average number in system, lambda is the arrival rate, and W is the mean
time each customer spends in the system.

## Main results

* `littlesLaw`          : the function `lam * W` representing L = lambda * W
* `littles_law_nonneg`  : `L >= 0` when `lambda >= 0` and `W >= 0`

## Why this lemma

Mathlib has no named `littles_law` or `queueing` declaration. Pythia exposes
the Little's Law product and its non-negativity so the `pythia` tactic cascade
can close queueing-analysis goals without the user reaching for the underlying
multiplication lemmas.

The companion empirical layer (`tools/sim/or_littles_law.py`) runs a 10 000-trial
PBT, a deterministic sweep, and a mutation harness so customers can verify the
non-negativity bound holds across realistic arrival-rate and sojourn-time ranges.

## References

* Little, J. D. C. "A Proof for the Queuing Formula L = lambda*W."
  *Operations Research* 9(3): 383-387 (1961).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.OR

/-- The Little's Law product `L = lam * W`, where `lam` is the arrival rate
and `W` is the mean sojourn time. Both arguments are unconstrained reals;
the meaningful domain is `lam >= 0` and `W >= 0`. -/
noncomputable def littlesLaw (lam W : ℝ) : ℝ := lam * W

/-- **Little's Law non-negativity.** For any non-negative arrival rate `lam`
and non-negative mean sojourn time `W`, the average number in system
`L = lam * W` is non-negative. This is the fundamental sign property of
Little's Law in a stable queueing system. -/
@[stat_lemma]
theorem littles_law_nonneg {lam W : ℝ} (hlam : 0 ≤ lam) (hW : 0 ≤ W) :
    0 ≤ littlesLaw lam W := by
  unfold littlesLaw
  exact mul_nonneg hlam hW

end Pythia.OR
