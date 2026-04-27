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

/-- Simp-normal-form companion for `am_gm_two`. `pythia`'s simp pass
unfolds `Real.sqrt (a*b)` to `Real.sqrt a * Real.sqrt b` under nonneg
hypotheses (Mathlib `Real.sqrt_mul`), so the original head-match is
gone before aesop reaches the ruleset. Tagging this rewritten form
keeps AM-GM reachable through the cascade. -/
@[stat_lemma]
theorem am_gm_two_split (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  rw [← Real.sqrt_mul ha]
  exact am_gm_two a b ha hb

/-! ## Markov inequality (Chebyshev's inequality) -/

-- `MeasureTheory.meas_ge_le_lintegral_div`:
--   For an AE-measurable f : alpha -> R>=0inf and epsilon != 0,
--   mu { omega | f omega >= epsilon } <= (integral f) / epsilon.
-- This is the canonical Markov (first-moment) inequality in Mathlib.
-- We retag it with `@[stat_lemma]` so the pythia tactic cascade
-- can close goals of that shape automatically.
attribute [stat_lemma] MeasureTheory.meas_ge_le_lintegral_div

/-! ## Cauchy-Schwarz (2 variables) -/

/-- **Cauchy-Schwarz inequality (two variables).**
For real numbers `a b c d`, the square of the inner product
`a * c + b * d` is at most the product of the squared norms
`(a^2 + b^2) * (c^2 + d^2)`.

The formal proof uses the discriminant identity `(a*d - b*c)^2 >= 0`,
which expands directly to the required inequality. No exotic Mathlib
lemmas are borrowed for this 2-variable form; the proof is entirely
self-contained. The `@[stat_lemma]` attribute registers this theorem
in the pythia tactic cascade. The retag of the inner-product form
`inner_mul_le_norm_mul_norm` is left for a follow-up batch. -/
@[stat_lemma]
theorem cauchy_schwarz_two (a b c d : ℝ) :
    (a * c + b * d)^2 ≤ (a^2 + b^2) * (c^2 + d^2) := by
  nlinarith [sq_nonneg (a*d - b*c), sq_nonneg (a*c + b*d), sq_nonneg a,
             sq_nonneg b, sq_nonneg c, sq_nonneg d]

end Pythia.MathlibTags
