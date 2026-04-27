/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RC Time Constant Positivity

The time constant of a first-order RC circuit is defined as
`tau = R * C`, where `R` is the resistance in ohms and `C` is the
capacitance in farads. When both are strictly positive, the time
constant is strictly positive.

## Main results

* `rcTimeConstant`          : the time constant function `R * C`
* `rc_time_constant_pos`    : `tau > 0` when `R > 0` and `C > 0`

## Why this lemma

Mathlib has `mul_pos` and real arithmetic but no named `rc_circuit`
declaration. Pythia exposes the RC time constant and its positivity
so the `pythia` tactic cascade can close transient-analysis goals
without the user reaching for the underlying multiplication lemmas.

The companion empirical layer (`tools/sim/engineering_rc_time_constant.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the closed-form bound holds across
realistic resistor (1 ohm to 10 M-ohm) and capacitor (1 pF to 1 mF)
parameter ranges.

## References

* Sedra, A. S. and Smith, K. C. "Microelectronic Circuits," 8th ed.
  Oxford University Press (2020), Section 1.6: First-Order Circuits.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Engineering

/-- The RC circuit time constant `tau = R * C`.
The arguments are unconstrained reals; the meaningful domain is
`R > 0` (resistance in ohms) and `C > 0` (capacitance in farads). -/
noncomputable def rcTimeConstant (R C : ℝ) : ℝ := R * C

/-- **RC time constant positivity.** For any strictly positive resistance
`R` and strictly positive capacitance `C`, the RC time constant
`tau = R * C` is strictly positive. This is the fundamental property
that makes the exponential transient response well-defined. -/
@[stat_lemma]
theorem rc_time_constant_pos {R C : ℝ} (hR : 0 < R) (hC : 0 < C) :
    0 < rcTimeConstant R C := by
  unfold rcTimeConstant
  exact mul_pos hR hC

end Pythia.Engineering
