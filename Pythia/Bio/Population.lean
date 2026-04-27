/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hardy-Weinberg Allele-Frequency Conservation

For a sexually reproducing diploid population with allele frequencies
`p` and `q` satisfying `p + q = 1`, the genotype frequencies
(homozygous dominant `p^2`, heterozygous `2pq`, homozygous recessive
`q^2`) sum to exactly 1.

## Main results

* `hardy_weinberg_conservation` : `p^2 + 2*p*q + q^2 = 1` when `p + q = 1`

## Why this lemma

Mathlib has no `hardy_weinberg` declaration. This is a pure algebraic
identity that falls out immediately from the constraint `p + q = 1`,
but naming and tagging it lets the `pythia` tactic cascade close
population-genetics goals without the user unfolding the constraint by
hand.

The companion empirical layer (`tools/sim/bio_hardy_weinberg.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the closed-form bound holds across
their own allele-frequency ranges.

## References

* Hardy, G. H. "Mendelian proportions in a mixed population."
  *Science* 28(706): 49-50 (1908).
* Weinberg, W. "Uber den Nachweis der Vererbung beim Menschen."
  *Jahresh. Verein f. vaterland. Naturkunde in Wurttemberg* 64: 368-382 (1908).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Bio.Population

/-- **Hardy-Weinberg conservation.** For allele frequencies `p` and `q`
satisfying `p + q = 1`, the three genotype frequencies
(homozygous dominant `p^2`, heterozygous `2pq`, homozygous recessive
`q^2`) partition the probability simplex: they sum to exactly 1.
This is the algebraic core of the Hardy-Weinberg equilibrium principle. -/
@[stat_lemma]
theorem hardy_weinberg_conservation (p q : ℝ) (h : p + q = 1) :
    p ^ 2 + 2 * p * q + q ^ 2 = 1 := by
  have hq : q = 1 - p := by linarith
  rw [hq]
  ring

end Pythia.Bio.Population
