/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ohm's Law Power Dissipation Non-Negativity

Power dissipated in a resistor is defined as `P = I^2 * R`, where `I`
is the current in amperes and `R` is the resistance in ohms. When the
resistance is non-negative, the power is non-negative.

## Main results

* `powerDissipation`           : the power function `I^2 * R`
* `power_dissipation_nonneg`   : `P >= 0` when `R >= 0`

## Why this lemma

Mathlib has `sq_nonneg` and `mul_nonneg` but no named `ohm` or
`power_dissipation` declaration. Pythia exposes the resistive power
dissipation and its non-negativity so the `pythia` tactic cascade can
close thermal-analysis goals without the user reaching for the
underlying multiplication lemmas.

The companion empirical layer (`tools/sim/engineering_power_dissipation.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the closed-form bound holds across
realistic current (plus or minus 100 A) and resistance (1 ohm to 1 M-ohm)
parameter ranges.

## References

* Ohm, G. S. "Die galvanische Kette, mathematisch bearbeitet."
  T. H. Riemann, Berlin (1827).
* Joule, J. P. "On the heat evolved by metallic conductors of
  electricity." Philosophical Magazine 19:260 (1841).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Engineering

/-- Power dissipated in a resistor: `P = I^2 * R`.
The arguments are unconstrained reals; the meaningful domain is
`R >= 0` (resistance in ohms) and `I` any real (current in amperes). -/
noncomputable def powerDissipation (I R : ℝ) : ℝ := I^2 * R

/-- **Ohm's law power dissipation non-negativity.** For any current `I`
and any non-negative resistance `R`, the power dissipated
`P = I^2 * R` is non-negative. This follows from the fact that `I^2`
is always non-negative and the product of two non-negatives is
non-negative. -/
@[stat_lemma]
theorem power_dissipation_nonneg (I : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ powerDissipation I R := by
  unfold powerDissipation
  exact mul_nonneg (sq_nonneg I) hR

end Pythia.Engineering
