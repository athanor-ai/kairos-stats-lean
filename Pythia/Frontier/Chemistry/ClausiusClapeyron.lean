/-
Pythia.Frontier.Chemistry.ClausiusClapeyron -- Clausius-Clapeyron
equation for the slope of a phase-coexistence curve.

Reference: Clausius, R. (1850). "Über die bewegende Kraft der Wärme
und die Gesetze, welche sich daraus für die Wärmelehre selbst
ableiten lassen." Annalen der Physik 79:368-397.

The Clausius-Clapeyron equation relates the slope of a phase
coexistence curve P(T) to the latent heat L of transition and the
volume change ΔV:

    dP/dT = L / (T * ΔV)

For vaporization (gas-liquid) with ideal-gas approximation
ΔV ≈ V_gas = RT/P, the equation integrates to

    ln(P2 / P1) = -(L / R) * (1/T2 - 1/T1)

For exothermic phase changes (L > 0) the saturation pressure rises
with T.
-/
import Mathlib

namespace Pythia.Frontier.Chemistry

/-- Integrated Clausius-Clapeyron: ratio of saturation pressures at
    two temperatures, for a phase transition with latent heat L,
    using the ideal-gas-vapor approximation. -/
noncomputable def clausiusClapeyronRatio (L R T1 T2 : ℝ) : ℝ :=
  Real.exp (-(L / R) * (1 / T2 - 1 / T1))

/-
For a phase transition with positive latent heat (L > 0), if
    T2 > T1 then the saturation pressure ratio P2/P1 > 1, i.e. the
    pressure increases with temperature.
-/
theorem clausiusClapeyron_pressure_increases_with_T
    {L R T1 T2 : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hT1 : 0 < T1) (hT12 : T1 < T2) :
    1 < clausiusClapeyronRatio L R T1 T2 := by
  exact lt_of_le_of_lt ( by norm_num ) ( Real.exp_lt_exp.mpr ( mul_lt_mul_of_neg_left ( sub_neg_of_lt <| one_div_lt_one_div_of_lt hT1 hT12 ) <| neg_neg_of_pos <| by positivity ) )

/-- Equal temperatures give a ratio of 1 (no pressure change). -/
theorem clausiusClapeyron_ratio_at_equal_T
    (L R T : ℝ) (hT : T ≠ 0) :
    clausiusClapeyronRatio L R T T = 1 := by
  unfold clausiusClapeyronRatio
  simp

end Pythia.Frontier.Chemistry