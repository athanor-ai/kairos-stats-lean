/-
Pythia.Chemistry.BeerLambert -- Beer-Lambert absorption law.

Reference: Beer, A. (1852). "Bestimmung der Absorption des rothen
Lichts in farbigen Flüssigkeiten." Annalen der Physik und Chemie
86:78-88.

The Beer-Lambert law relates the absorbance A of a solution to its
concentration c, path length l, and molar absorptivity ε:

    A = ε * c * l

A is linear in c at fixed (ε, l), linear in l at fixed (ε, c), and
nonneg whenever ε, c, l ≥ 0.
-/
import Mathlib

namespace Pythia.Chemistry

/-- Beer-Lambert absorbance: A = ε * c * l. -/
def beerLambertAbsorbance (epsilon c l : ℝ) : ℝ := epsilon * c * l

/-- Absorbance is monotone increasing in concentration for ε, l ≥ 0. -/
theorem beerLambert_monotone_in_concentration
    {epsilon l c1 c2 : ℝ}
    (hε : 0 ≤ epsilon) (hl : 0 ≤ l) (hc : c1 ≤ c2) :
    beerLambertAbsorbance epsilon c1 l ≤ beerLambertAbsorbance epsilon c2 l := by
  unfold beerLambertAbsorbance
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc hε) hl

/-- Absorbance is nonneg when all parameters are nonneg. -/
theorem beerLambert_nonneg
    {epsilon c l : ℝ}
    (hε : 0 ≤ epsilon) (hc : 0 ≤ c) (hl : 0 ≤ l) :
    0 ≤ beerLambertAbsorbance epsilon c l := by
  unfold beerLambertAbsorbance
  exact mul_nonneg (mul_nonneg hε hc) hl

/-- Doubling the path length doubles the absorbance. -/
theorem beerLambert_doubles_with_path_length
    (epsilon c l : ℝ) :
    beerLambertAbsorbance epsilon c (2 * l) =
      2 * beerLambertAbsorbance epsilon c l := by
  unfold beerLambertAbsorbance
  ring

end Pythia.Chemistry
