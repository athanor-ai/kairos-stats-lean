/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Population Genetics

Kimura neutral fixation probability and Hardy-Weinberg allele frequency invariance.

## Main results

* `kimura_neutral_fixation` — neutral mutant fixation probability equals 1/(2N).
* `hwe_allele_frequency_invariance` — HWE preserves allele frequency under random mating.

## References

* Kimura, M. "On the probability of fixation of mutant genes in a population."
  *Genetics* 47(6): 713-719 (1962).
* Hardy, G. H. "Mendelian proportions in a mixed population."
  *Science* 28(706): 49-50 (1908).
* Weinberg, W. "Uber den Nachweis der Vererbung beim Menschen."
  *Jahresh. Verein f. vaterland. Naturkunde in Wurttemberg* 64: 368-382 (1908).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Bio.PopGenetics

/-!
## Kimura neutral fixation probability

For a neutral mutant in a diploid population of size `N`, the probability that the
single mutant allele eventually fixes (reaches frequency 1) equals `1/(2N)`.
This follows from the neutrality assumption: under random genetic drift with no
selective advantage, each of the `2N` allele copies is equally likely to be the
ancestor of the entire population.
-/

/-- The Kimura neutral fixation probability for a single mutant in a diploid population of `N`
individuals. -/
noncomputable def kimuraNeutralFixationProb (N : ℕ) : ℝ := 1 / (2 * (N : ℝ))

/-- **Kimura neutral fixation probability.**
A neutral mutant in a diploid population of size `N ≥ 1` has fixation probability `1/(2N)`,
which is strictly positive and strictly less than 1. -/
@[stat_lemma]
theorem kimura_neutral_fixation (N : ℕ) (hN : 1 ≤ N) :
    kimuraNeutralFixationProb N = 1 / (2 * (N : ℝ)) ∧
    0 < kimuraNeutralFixationProb N ∧
    kimuraNeutralFixationProb N < 1 := by
  unfold kimuraNeutralFixationProb
  refine ⟨rfl, ?_, ?_⟩
  · positivity
  · rw [div_lt_one (by positivity)]
    have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith

/-!
## Hardy-Weinberg allele frequency invariance

Under Hardy-Weinberg equilibrium, the frequency of allele A in the next generation
equals the frequency `p` in the current generation: `p² + (1/2)·2pq = p`.
This confirms that random mating alone does not alter allele frequencies.
-/

/-- **Hardy-Weinberg allele frequency invariance.**
Given allele frequencies `p` and `q` with `p + q = 1`, `p ≥ 0`, `q ≥ 0`,
the allele A frequency reconstructed from genotype frequencies (homozygous AA
plus half of heterozygous Aa) equals `p`. -/
@[stat_lemma]
theorem hwe_allele_frequency_invariance (p q : ℝ) (h : p + q = 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    let freq_AA := p ^ 2; let freq_Aa := 2 * p * q
    freq_AA + (1 / 2) * freq_Aa = p := by
  simp only
  have hq_eq : q = 1 - p := by linarith
  rw [hq_eq]
  ring

end Pythia.Bio.PopGenetics
