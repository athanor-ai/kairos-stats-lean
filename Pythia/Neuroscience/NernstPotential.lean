/-
Pythia.Neuroscience.NernstPotential -- Nernst equilibrium potential
for an ion across a membrane.

Reference: Nernst, W. (1888). "Zur Kinetik der in Lösung befindlichen
Körper." Z. Phys. Chem. 2:613-637.

For an ion with valence z, the Nernst equilibrium potential is

  E_Nernst = (RT / zF) * ln([ion]_out / [ion]_in)

This is the membrane voltage at which the electrochemical gradient
balances the concentration gradient. The sign of E_Nernst follows the
concentration ratio for cations (z > 0) and reverses for anions.
-/
import Mathlib

namespace Pythia.Neuroscience

/-- The Nernst equilibrium potential. R is the gas constant, T is
absolute temperature, z is ion valence, F is the Faraday constant. -/
noncomputable def nernstPotential (R T : ℝ) (z : ℝ) (F : ℝ)
    (ionOut ionIn : ℝ) : ℝ :=
  (R * T / (z * F)) * Real.log (ionOut / ionIn)

/-- For a positive valence (cation) with [out] > [in], the Nernst
potential is strictly positive: cations flow inward to equilibrate. -/
theorem nernstPotential_pos_for_cation
    {R T z F ionOut ionIn : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hz : 0 < z) (hF : 0 < F)
    (hIn : 0 < ionIn) (hRatio : ionIn < ionOut) :
    0 < nernstPotential R T z F ionOut ionIn := by
  unfold nernstPotential
  have hcoeff : 0 < R * T / (z * F) := by positivity
  have hRatio_gt_one : 1 < ionOut / ionIn :=
    (one_lt_div hIn).mpr hRatio
  have hlog_pos : 0 < Real.log (ionOut / ionIn) :=
    Real.log_pos hRatio_gt_one
  exact mul_pos hcoeff hlog_pos

/-- Nernst potential is zero when concentrations are equal. -/
theorem nernstPotential_zero_at_equilibrium
    (R T z F ion : ℝ) (hion : 0 < ion) :
    nernstPotential R T z F ion ion = 0 := by
  unfold nernstPotential
  rw [div_self (ne_of_gt hion), Real.log_one, mul_zero]

end Pythia.Neuroscience
