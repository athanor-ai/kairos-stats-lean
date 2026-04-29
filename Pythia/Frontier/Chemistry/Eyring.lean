/-
Pythia.Frontier.Chemistry.Eyring -- Eyring transition-state theory
rate equation.

Reference: Eyring, H. (1935). "The activated complex in chemical
reactions." J. Chem. Phys. 3:107-115.

Transition-state theory expresses the rate constant of an elementary
reaction as

    k = κ * (k_B T / h) * exp(-ΔG‡ / (R T))

where κ is the transmission coefficient, k_B is Boltzmann's constant,
h is Planck's constant, T is absolute temperature, and ΔG‡ is the
Gibbs energy of activation. The Arrhenius form k = A * exp(-Ea/RT)
emerges by absorbing the prefactor and the entropic part of ΔG‡
into the Arrhenius A.
-/
import Mathlib

namespace Pythia.Frontier.Chemistry

/-- Eyring rate constant. -/
noncomputable def eyringRate (kappa kB h T deltaG R : ℝ) : ℝ :=
  kappa * (kB * T / h) * Real.exp (-deltaG / (R * T))

/-- The Eyring rate is strictly positive for κ, kB, T, h, R > 0
    and any ΔG‡. -/
theorem eyringRate_pos
    {kappa kB h T deltaG R : ℝ}
    (hκ : 0 < kappa) (hkB : 0 < kB) (hh : 0 < h)
    (hT : 0 < T) (hR : 0 < R) :
    0 < eyringRate kappa kB h T deltaG R := by
  sorry

/-- Lowering the activation barrier ΔG‡ strictly increases the rate
    (with all other parameters fixed). -/
theorem eyringRate_decreasing_in_deltaG
    {kappa kB h T deltaG1 deltaG2 R : ℝ}
    (hκ : 0 < kappa) (hkB : 0 < kB) (hh : 0 < h)
    (hT : 0 < T) (hR : 0 < R) (hΔG : deltaG1 ≤ deltaG2) :
    eyringRate kappa kB h T deltaG2 R ≤ eyringRate kappa kB h T deltaG1 R := by
  sorry

end Pythia.Frontier.Chemistry
