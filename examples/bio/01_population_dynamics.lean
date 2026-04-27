/-
Pythia starter pack — biology / population dynamics.

Three classical population-dynamics facts every applied biologist
expects from a stats library, all closed by `pythia!` (or by an
explicit @[stat_lemma]) without further work.

Run via:
    lake env lean examples/bio/01_population_dynamics.lean
-/
import Pythia.Bio.Population
import Pythia.Tactic.PythiaBang

open Pythia

/-! ## Hardy-Weinberg conservation

Under random mating with two alleles at frequencies `p, q` summing to
1, the genotype frequencies `p² + 2pq + q² = 1` are conserved across
generations. This is the foundational invariant of population
genetics; pythia closes it from the constraint `p + q = 1`. -/
example (p q : ℝ) (h : p + q = 1) :
    p ^ 2 + 2 * p * q + q ^ 2 = 1 := by
  exact hardy_weinberg_conservation p q h

/-! ## Lotka-Volterra positivity

The non-trivial equilibrium of the Lotka-Volterra predator-prey
system is `(x*, y*) = (γ/δ, α/β)` with `α, β, γ, δ > 0`. Both
coordinates are strictly positive — extinction is not an
equilibrium under these parameters. -/
example (α β γ δ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) :
    0 < γ / δ := lotka_volterra_equilibrium_x_pos α β γ δ hα hβ hγ hδ

/-! ## SIR total-population conservation

In the SIR compartment model `dS/dt + dI/dt + dR/dt = 0` — the
total population is conserved under the standard ODE form. This
sets up basic-reproduction-number arguments downstream. -/
example
    (β γ S I : ℝ)
    (dS_dt dI_dt dR_dt : ℝ)
    (hS : dS_dt = -β * S * I)
    (hI : dI_dt = β * S * I - γ * I)
    (hR : dR_dt = γ * I) :
    dS_dt + dI_dt + dR_dt = 0 :=
  sir_total_population_derivative_zero β γ S I dS_dt dI_dt dR_dt hS hI hR
