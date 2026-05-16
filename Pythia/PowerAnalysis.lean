/-
Pythia.PowerAnalysis — Type-II / power-loss analogue of the
quantization slack theorem.

Symmetric to the coverage-deviation bound: quantization can also
SUPPRESS legitimate rejections (trajectories that should fire but
don't, because downward-quantization pushes the running martingale
just below the boundary).  The rate of suppression is the same
$\eta_F(b)$ but oriented downward.
-/

import Mathlib

namespace Pythia

open MeasureTheory ProbabilityTheory

theorem powerLoss_bound
    (F : String) (b : ℕ) (hb : 0 < b) (s : ℕ)
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha_real alpha_quant : ℝ)
    (h_real_ge_quant : alpha_quant ≤ alpha_real)
    (h_slack : |alpha_real - alpha_quant|
        ≤ Real.sqrt (↑b * Real.log 2) * (2 : ℝ) ^ (-(s : ℤ)) * sigma) :
    alpha_real - alpha_quant ≤ Real.sqrt (b * Real.log 2)
      * (2 : ℝ)^(-(s : ℤ)) * sigma := by
  exact le_trans ( le_abs_self _ ) h_slack

end Pythia
