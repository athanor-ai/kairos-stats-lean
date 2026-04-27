/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Signal Energy Non-Negativity

The energy of a discrete-time signal `x : Fin n -> R` is defined as
`E = sum_i (x i)^2`. This module proves that energy is always
non-negative.

## Main results

* `signalEnergy`          : the signal energy function `sum i, (x i)^2`
* `signal_energy_nonneg`  : `E >= 0` for any signal `x`

## Why this lemma

Mathlib has `Finset.sum_nonneg` and `sq_nonneg` but no named
`signalEnergy` declaration. Pythia exposes the discrete-time energy
definition and its non-negativity so the `pythia` tactic cascade can
close energy-lower-bound goals without the user reaching for the
underlying summation lemmas.

The companion empirical layer (`tools/sim/engineering_signal_energy.py`)
runs a 2 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the bound holds across realistic
signal lengths (1 to 100 samples) and amplitude scales (0.1 to 10).

## References

* Oppenheim, A. V. and Schafer, R. W. "Discrete-Time Signal Processing,"
  3rd ed. Prentice Hall (2010), Section 2.4: Signal Energy.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Engineering

/-- The energy of a discrete-time signal `x : Fin n -> R`,
defined as the sum of squared sample values. -/
noncomputable def signalEnergy {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i)^2

/-- **Signal energy non-negativity.** For any discrete-time signal
`x : Fin n -> R`, the signal energy `E = sum_i (x i)^2` is
non-negative. This is the fundamental property that makes energy
a valid measure of signal power. -/
@[stat_lemma]
theorem signal_energy_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ signalEnergy x := by
  unfold signalEnergy
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

end Pythia.Engineering
