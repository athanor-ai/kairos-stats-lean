/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Henderson-Hasselbalch Buffer pH

The Henderson-Hasselbalch equation `pH = pKa + log10([A-]/[HA])` gives
the pH of a buffer solution as a function of the acid dissociation
constant pKa and the base-to-acid concentration ratio. Here `[A-]` is
the conjugate-base concentration and `[HA]` is the weak-acid
concentration; the ratio `[A-]/[HA]` is a positive real.

## Main results

* `hhPH`               : the buffer pH as `pKa + log10(ratio)`
* `hh_monotone_in_ratio` : pH is monotone-increasing in the ratio

## Why this lemma

Mathlib provides `Real.logb_le_logb_right` and related monotonicity
lemmas for the general logarithm but has no named
`henderson_hasselbalch` declaration. Pythia exposes the definition and
its monotonicity so the `pythia` tactic cascade can close buffer-pH
goals directly without the user unfolding the logarithm by hand.

The companion empirical layer (`tools/sim/chemistry_henderson_hasselbalch.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation harness
so customers can verify the monotonicity bound holds across realistic
parameter ranges.

## References

* Henderson, L. J. "Concerning the relationship between the strength of
  acids and their capacity to preserve neutrality." *American Journal of
  Physiology* 21(2): 173-179 (1908).
* Hasselbalch, K. A. "Die Berechnung der Wasserstoffzahl des Blutes aus
  der freien und gebundenen Kohlensaure desselben." *Biochemische
  Zeitschrift* 78: 112-144 (1917).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Chemistry

/-- The Henderson-Hasselbalch buffer pH: `pH = pKa + log10(ratio)`.
The `ratio` is the base-to-acid concentration ratio `[A-]/[HA]`;
the meaningful domain is `ratio > 0`. -/
noncomputable def hhPH (pKa ratio : ℝ) : ℝ := pKa + Real.logb 10 ratio

/-- **pH monotonicity.** For any fixed pKa, the Henderson-Hasselbalch
pH is monotone-increasing in the base-to-acid ratio: if `r1 <= r2`
and `0 < r1`, then `hhPH pKa r1 <= hhPH pKa r2`. -/
@[stat_lemma]
theorem hh_monotone_in_ratio (pKa : ℝ) {r1 r2 : ℝ} (hr1 : 0 < r1) (hle : r1 ≤ r2) :
    hhPH pKa r1 ≤ hhPH pKa r2 := by
  unfold hhPH
  have hr2 : (0 : ℝ) < r2 := lt_of_lt_of_le hr1 hle
  have h1lt : (1 : ℝ) < 10 := by norm_num
  linarith [Real.logb_le_logb_of_le h1lt hr1 hle]

end Pythia.Chemistry
