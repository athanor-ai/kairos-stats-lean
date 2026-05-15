/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Accelerated Gradient Descent (Nesterov's method)

Convergence rate: f(x_k) - f* <= 2LD^2/(k+1)^2. The quadratic
improvement over standard GD is the hallmark of momentum methods.

## References

* Nesterov, Y. (1983). "A method for solving a convex programming
  problem with convergence rate O(1/k^2)." Soviet Mathematics Doklady
  27(2).
* Nesterov, Y. (2004). "Introductory Lectures on Convex Optimization."
  Springer, Theorem 2.2.3.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.AcceleratedGradient

/-- Nesterov's convergence bound: 2LD^2/(k+1)^2. -/
noncomputable def nesterovBound (L D : ℝ) (k : ℕ) : ℝ :=
  2 * L * D ^ 2 / ((k : ℝ) + 1) ^ 2

theorem nesterovBound_pos {L D : ℝ} (hL : 0 < L) (hD : 0 < D) (k : ℕ) :
    0 < nesterovBound L D k := by
  simp only [nesterovBound]
  apply div_pos
  · exact mul_pos (mul_pos (by norm_num) hL) (sq_pos_of_pos hD)
  · positivity

/-- Nesterov's bound is O(1/k^2): it tends to 0 as k -> infty. -/
theorem nesterovBound_tendsto {L D : ℝ} (hL : 0 < L) (hD : 0 < D) :
    Filter.Tendsto (nesterovBound L D) Filter.atTop (nhds 0) := by
  unfold nesterovBound
  have hk1 : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop_iff.mpr (by norm_num : 2 ≠ 0)).comp hk1
  exact tendsto_const_nhds.div_atTop h1

/-- Nesterov's bound improves quadratically over GD bound 2LD^2/(k+2):
for k >= 1, 1/(k+1)^2 <= 1/(k+2). -/
@[stat_lemma]
theorem nesterov_beats_gd {L D : ℝ} (hL : 0 < L) (hD : 0 < D) (k : ℕ) (hk : 1 ≤ k) :
    nesterovBound L D k ≤ 2 * L * D ^ 2 / ((k : ℝ) + 2) := by
  simp only [nesterovBound]
  apply div_le_div_of_nonneg_left
  · positivity
  · positivity
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
    nlinarith [sq_nonneg ((k : ℝ) + 1)]

/-- Momentum coefficient: t_{k+1} = (1 + sqrt(1 + 4*t_k^2)) / 2
satisfies t_{k+1}^2 - t_{k+1} <= t_k^2. Algebraic identity. -/
@[stat_lemma]
theorem momentum_coefficient_identity {tk tk1 : ℝ}
    (htk : 0 < tk) (htk1 : 0 < tk1)
    (h : 2 * tk1 = 1 + Real.sqrt (1 + 4 * tk ^ 2)) :
    tk1 ^ 2 - tk1 ≤ tk ^ 2 := by
  have hsq : (2 * tk1 - 1) ^ 2 = 1 + 4 * tk ^ 2 := by
    have hge : 1 + 4 * tk ^ 2 ≥ 0 := by nlinarith [sq_nonneg tk]
    have h2 : 2 * tk1 - 1 = Real.sqrt (1 + 4 * tk ^ 2) := by linarith
    rw [h2]
    exact Real.sq_sqrt (by linarith [sq_nonneg tk])
  nlinarith [sq_nonneg tk1]

end Pythia.Optimization.AcceleratedGradient
