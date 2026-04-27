/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CRRA Marginal Utility Positivity

The CRRA (constant relative risk aversion) utility function is
`u(c) = c^(1-γ) / (1-γ)` for risk-aversion parameter γ ≠ 1 and
consumption `c > 0`. Its marginal utility (first derivative) is
`u'(c) = c^(-γ)`.

## Main results

* `crraMarginalUtility`          : the marginal utility function `c^(-γ)`
* `crra_marginal_utility_pos`    : `u'(c) > 0` for all `c > 0` and any `γ`

## Why this lemma

Mathlib has `Real.rpow` and `Real.rpow_pos_of_pos` but no named
`crra` or `risk_aversion` declaration. Pythia exposes the CRRA
marginal utility and its positivity so the `pythia` tactic cascade
can close welfare-analysis goals without the user reaching for the
underlying real-power lemmas.

The companion empirical layer (`tools/sim/economics_crra.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the closed-form bound holds across
risk-loving (γ < 0), risk-neutral (γ = 0), and risk-averse (γ > 0)
parameter ranges.

## References

* Pratt, J. W. "Risk Aversion in the Small and in the Large."
  *Econometrica* 32(1-2): 122-136 (1964).
* Arrow, K. J. "Aspects of the Theory of Risk-Bearing."
  Yrjo Jahnsson Lectures, Helsinki (1965).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Economics

/-- The CRRA marginal utility function `u'(c) = c^(-γ)`.
The arguments are unconstrained reals; the meaningful domain is
`c > 0` and `γ ∈ ℝ` (γ ≠ 1 for the underlying utility to be
well-defined, but positivity holds for all γ). -/
noncomputable def crraMarginalUtility (gamma c : ℝ) : ℝ := c ^ (-gamma)

/-- **Marginal utility positivity.** For any risk-aversion parameter
`γ` and any strictly positive consumption level `c`, the CRRA
marginal utility `c^(-γ)` is strictly positive. This is the
first-order condition that makes CRRA utility increasing in
consumption. -/
@[stat_lemma]
theorem crra_marginal_utility_pos (gamma : ℝ) {c : ℝ} (hc : 0 < c) :
    0 < crraMarginalUtility gamma c := by
  unfold crraMarginalUtility
  exact Real.rpow_pos_of_pos hc _

end Pythia.Economics
