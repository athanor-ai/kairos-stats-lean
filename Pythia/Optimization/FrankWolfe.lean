/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Frank-Wolfe (Conditional Gradient) Convergence

Convergence rate: f(x_k) - f(x*) <= 2LD^2/(k+2).

## References

* Frank, M. and Wolfe, P. (1956). Naval Research Logistics 3(1-2).
* Jaggi, M. (2013). ICML 2013.
-/
import Mathlib

namespace Pythia.Optimization.FrankWolfe

structure FWParams where
  L : ℝ
  D : ℝ
  hL : 0 < L
  hD : 0 < D

noncomputable def convergenceBound (p : FWParams) (k : ℕ) : ℝ :=
  2 * p.L * p.D ^ 2 / ((k : ℝ) + 2)

theorem convergenceBound_pos (p : FWParams) (k : ℕ) :
    0 < convergenceBound p k := by
  simp only [convergenceBound]
  refine div_pos ?_ (by linarith [Nat.cast_nonneg (α := ℝ) k])
  exact mul_pos (mul_pos (show (0:ℝ) < 2 by norm_num) p.hL)
    (show (0:ℝ) < p.D ^ 2 by rw [sq]; exact mul_pos p.hD p.hD)

theorem convergenceBound_antitone (p : FWParams) :
    Antitone (convergenceBound p) := by
  intro a b hab
  simp only [convergenceBound]
  refine div_le_div_of_nonneg_left ?_ (by linarith [Nat.cast_nonneg (α := ℝ) a])
    (by linarith [Nat.cast_le (α := ℝ) |>.mpr hab])
  exact le_of_lt (mul_pos (mul_pos (show (0:ℝ) < 2 by norm_num) p.hL)
    (show (0:ℝ) < p.D ^ 2 by rw [sq]; exact mul_pos p.hD p.hD))

theorem convergenceBound_tendsto_zero (p : FWParams) :
    Filter.Tendsto (convergenceBound p) Filter.atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

end Pythia.Optimization.FrankWolfe
