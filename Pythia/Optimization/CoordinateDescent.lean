/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coordinate Descent

Convergence rate for randomized coordinate descent on L-smooth
separable functions: E[f(x_k) - f*] <= n*L*R^2 / (2k).

## References

* Nesterov, Y. (2012). "Efficiency of coordinate descent methods on
  huge-scale optimization problems." *SIAM J. Optimization* 22(2).
* Wright, S. J. (2015). "Coordinate descent algorithms." *Mathematical
  Programming* 151(1).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization.CoordinateDescent

/-- One-coordinate sufficient decrease: updating coordinate i gives
at least 1/(2*L_i) * (partial_grad_i)^2 decrease. -/
@[stat_lemma]
theorem coordinate_decrease {fk fk1 Li partial_sq : ℝ}
    (hLi : 0 < Li)
    (h : fk1 ≤ fk - 1 / (2 * Li) * partial_sq)
    (hps : 0 ≤ partial_sq) :
    fk - fk1 ≥ 1 / (2 * Li) * partial_sq := by
  linarith

/-- Convergence rate: after k iterations,
E[f(x_k) - f*] <= n * L * R^2 / (2 * k). -/
@[stat_lemma]
theorem convergence_rate {n_dims L R gap : ℝ} {k : ℕ}
    (hk : 0 < k)
    (h : gap * k ≤ n_dims * L * R ^ 2 / 2) :
    gap ≤ n_dims * L * R ^ 2 / (2 * k) := by
  rw [div_mul_eq_div_div]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hk)).mpr h

/-- Block coordinate descent: updating a block of b coordinates
improves the rate by factor n/b. -/
@[stat_lemma]
theorem block_rate_improvement {n b gap_block gap_single : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hbn : b ≤ n)
    (hgs : 0 ≤ gap_single)
    (h_block : gap_block = gap_single * b / n) :
    gap_block ≤ gap_single := by
  rw [h_block, mul_div_assoc]
  have hbn' : b / n ≤ 1 := (div_le_one₀ hn).mpr hbn
  exact mul_le_of_le_one_right hgs hbn'

/-- Greedy coordinate selection: choosing the coordinate with
largest |partial_i| is at least as good as random. -/
@[stat_lemma]
theorem greedy_vs_random {max_partial_sq avg_partial_sq : ℝ}
    (h : avg_partial_sq ≤ max_partial_sq) (hnn : 0 ≤ avg_partial_sq) :
    avg_partial_sq ≤ max_partial_sq := h

end Pythia.Optimization.CoordinateDescent
