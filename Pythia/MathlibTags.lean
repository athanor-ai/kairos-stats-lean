/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mathlib Retag Module

This module retags or proves direct corollaries of Mathlib lemmas
under the `@[stat_lemma]` attribute so the pythia tactic cascade
discovers them automatically. The formal content lives in Mathlib;
pythia adds the registry entry and, via `tools/sim/`, an empirical
harness that validates the bound numerically across realistic parameter
ranges and runs a mutation test to confirm the test set is not vacuous.

## Main results

* `am_gm_two` : `sqrt(a * b) <= (a + b) / 2` for any `a b : Real` with
  `0 <= a` and `0 <= b`. The 2-variable arithmetic-geometric mean
  inequality.

## References

* The AM-GM inequality for two non-negative reals traces back to
  Cauchy, A.-L. "Cours d'Analyse." Paris (1821), Chapter 1.
* Mathlib: `Mathlib.Analysis.MeanInequalities` for the general weighted
  form `geom_mean_le_arith_mean2_weighted`.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.MathlibTags

/-- **Arithmetic-Geometric Mean inequality (two variables).**
For non-negative reals `a` and `b`, the geometric mean `sqrt(a * b)`
is at most the arithmetic mean `(a + b) / 2`.

The formal proof uses `(sqrt a - sqrt b)^2 >= 0` and the Mathlib
lemmas `Real.mul_self_sqrt` and `Real.sqrt_mul`. The `@[stat_lemma]`
attribute registers this theorem in the pythia tactic cascade so that
goals of the form `sqrt (a * b) <= (a + b) / 2` close automatically. -/
@[stat_lemma]
theorem am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h_sq_nonneg : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have h_sa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
  have h_sb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb
  have h_sab : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) :=
    (Real.sqrt_mul ha b).symm
  nlinarith [h_sq_nonneg, h_sa, h_sb, h_sab]

end Pythia.MathlibTags
