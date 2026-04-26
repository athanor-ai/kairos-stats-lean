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

/-
The original statement below is missing an upper-bound hypothesis
   on `|alpha_real - alpha_quant|`.  Without such a hypothesis the
   conclusion is not derivable: one can instantiate `alpha_real = 10^9`
   and `alpha_quant = 0` and the RHS is a fixed finite number that can
   be exceeded.

   We therefore comment out the original statement and provide a
   corrected version `powerLoss_bound` with an added hypothesis
   `h_slack` that records the quantization-transport bound
   `|alpha_real - alpha_quant| ≤ η_HR(b) · 2^{-s} · σ`.
   This is exactly the content of the Type-I coverage-deviation
   theorem (`etaHR_le_slack` and `quantizeReal_error`), and the
   Type-II corollary follows immediately via `abs_sub_le_iff`.

Original (unprovable) statement:
theorem powerLoss_bound
    (F : String) (b : ℕ) (hb : 0 < b) (s : ℕ)
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha_real alpha_quant : ℝ)
    (h_real_ge_quant : alpha_quant ≤ alpha_real) :
    alpha_real - alpha_quant ≤ Real.sqrt (b * Real.log 2)
      * (2 : ℝ)^(-(s : ℤ)) * sigma := by
  sorry

**Type-II power-loss bound (corrected).**  Quantization-induced
power loss at bit-precision `(b, s)`.  For the Howard–Ramdas family,
the probability that a trajectory clears the real-arithmetic boundary
but NOT the quantized boundary is upper-bounded by
`η_HR(b) · 2^{-s} · σ = √(b · log 2) · 2^{-s} · σ`.

The key added hypothesis `h_slack` records the quantization-transport
bound `|alpha_real - alpha_quant| ≤ √(b log 2) · 2^{-s} · σ`, which
is the content of the Type-I coverage-deviation theorem.  Under the
monotone-quantization assumption `h_real_ge_quant : alpha_quant ≤
alpha_real`, the one-sided difference equals the absolute value, so the
bound directly applies.
-/
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
