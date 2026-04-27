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

/-!
## Lotka-Volterra (Lotka 1925, Volterra 1926)

The continuous predator-prey system

    dx/dt = alpha * x - beta * x * y
    dy/dt = delta * x * y - gamma * y

with `alpha, beta, gamma, delta > 0` admits a unique coexistence equilibrium

    x* = gamma / delta,    y* = alpha / beta.

Both coordinates are strictly positive whenever the four rate parameters are
strictly positive. The positivity results below are the algebraic core that
downstream stability analyses build on.

References:
* Lotka, A. J. "Elements of Physical Biology." Williams and Wilkins (1925).
* Volterra, V. "Variazioni e fluttuazioni del numero d'individui in specie
  animali conviventi." Mem. R. Accad. Naz. dei Lincei, Ser. VI, 2: 31-113 (1926).
-/

/-- Coexistence equilibrium prey density: `x* = gamma / delta`. -/
noncomputable def lotkaVolterraEquilibriumX (gamma delta : ℝ) : ℝ := gamma / delta

/-- Coexistence equilibrium predator density: `y* = alpha / beta`. -/
noncomputable def lotkaVolterraEquilibriumY (alpha beta : ℝ) : ℝ := alpha / beta

/-- **Lotka-Volterra prey equilibrium positivity.**
When `gamma > 0` and `delta > 0`, the coexistence prey density `x* = gamma / delta`
is strictly positive. -/
@[stat_lemma]
theorem lotka_volterra_equilibrium_x_pos
    (gamma delta : ℝ) (hgamma : 0 < gamma) (hdelta : 0 < delta) :
    0 < lotkaVolterraEquilibriumX gamma delta := by
  unfold lotkaVolterraEquilibriumX
  exact div_pos hgamma hdelta

/-- **Lotka-Volterra predator equilibrium positivity.**
When `alpha > 0` and `beta > 0`, the coexistence predator density `y* = alpha / beta`
is strictly positive. -/
@[stat_lemma]
theorem lotka_volterra_equilibrium_y_pos
    (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < lotkaVolterraEquilibriumY alpha beta := by
  unfold lotkaVolterraEquilibriumY
  exact div_pos halpha hbeta

end Pythia.Bio.Population
