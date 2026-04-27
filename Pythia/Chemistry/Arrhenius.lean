/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Arrhenius Rate Constant

The Arrhenius equation `k(T) = A * exp(-Eₐ / (R * T))` gives the
reaction rate constant as a function of temperature. The pre-exponential
factor `A > 0` and activation energy `Eₐ >= 0` are empirical parameters;
`R > 0` is the universal gas constant; `T > 0` is absolute temperature.

## Main results

* `arrhenius`     : the rate constant `A * exp(-Eₐ / (R * T))`
* `arrhenius_pos` : `k > 0` whenever `A > 0`, `T > 0`, and `R > 0`

## Why this lemma

Mathlib provides `Real.exp_pos` and `mul_pos` but has no named
`arrhenius` declaration. Pythia exposes the rate constant and its
positivity so the `pythia` tactic cascade can close goals about it
directly without the user unfolding the exponential by hand.

The companion empirical layer (`tools/sim/chemistry_arrhenius.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the positivity bound holds across
realistic parameter ranges.

## References

* Arrhenius, S. "Uber die Reaktionsgeschwindigkeit bei der Inversion
  von Rohrzucker durch Sauren." *Z. Phys. Chem.* 4: 226-248 (1889).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Chemistry

/-- The Arrhenius rate constant `k = A * exp(-Eₐ / (R * T))`.
The arguments are unconstrained reals; the meaningful domain is
`A > 0`, `Eₐ >= 0`, `R > 0`, `T > 0`. -/
noncomputable def arrhenius (A Ea R T : ℝ) : ℝ :=
  A * Real.exp (-(Ea / (R * T)))

/-- **Rate constant positivity.** For any activation energy `Eₐ`,
the Arrhenius rate constant is strictly positive whenever the
pre-exponential factor `A`, the gas constant `R`, and the absolute
temperature `T` are all strictly positive. -/
@[stat_lemma]
theorem arrhenius_pos {A Ea R T : ℝ} (hA : 0 < A) (_hT : 0 < T) (_hR : 0 < R) :
    0 < arrhenius A Ea R T := by
  unfold arrhenius
  exact mul_pos hA (Real.exp_pos _)

end Pythia.Chemistry
