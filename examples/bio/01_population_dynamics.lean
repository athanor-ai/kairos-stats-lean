/-
Pythia starter pack: biology / population dynamics.

Three classical population-dynamics facts every applied biologist
expects from a stats library. All three are tagged `@[stat_lemma]`
in `Pythia.Bio.Population`, so the headline `pythia!` tactic closes
them via the @[stat_lemma] aesop ruleset.

Run via:
    lake env lean examples/bio/01_population_dynamics.lean
-/
import Pythia.Bio.Population
import Pythia.Tactic.PythiaBang

open Pythia.Bio.Population

/-! ## Hardy-Weinberg conservation

Under random mating with two alleles at frequencies `p, q` summing to
`1`, the genotype frequencies satisfy `p² + 2pq + q² = 1`. The
foundational invariant of population genetics. -/
example (p q : ℝ) (h : p + q = 1) :
    p ^ 2 + 2 * p * q + q ^ 2 = 1 := by
  pythia!

-- Equivalent named-theorem form:
example (p q : ℝ) (h : p + q = 1) :
    p ^ 2 + 2 * p * q + q ^ 2 = 1 :=
  hardy_weinberg_conservation p q h

/-! ## Lotka-Volterra prey equilibrium positivity

The non-trivial equilibrium of the Lotka-Volterra predator-prey
system has prey-coordinate `γ/δ`, exposed in pythia as
`lotkaVolterraEquilibriumX gamma delta`. With `γ, δ > 0` it is
strictly positive (extinction is not an equilibrium under these
parameters). -/
example (gamma delta : ℝ) (hgamma : 0 < gamma) (hdelta : 0 < delta) :
    0 < lotkaVolterraEquilibriumX gamma delta := by
  pythia!

/-! ## SIR total-population conservation

In the standard SIR compartment model `dS + dI + dR = 0` along the
trajectory: total population is conserved. The downstream
basic-reproduction-number arguments build on this invariant. -/
example {beta gamma S I dS dI dR : ℝ}
    (hS : dS = -beta * S * I)
    (hI : dI = beta * S * I - gamma * I)
    (hR : dR = gamma * I) :
    dS + dI + dR = 0 := by
  pythia!
