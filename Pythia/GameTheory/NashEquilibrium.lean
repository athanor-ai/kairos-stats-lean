/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nash Equilibrium (algebraic identities)

A strategy profile (x*, y*) is a Nash equilibrium if no player
can improve by unilateral deviation. For 2-player zero-sum games,
Nash equilibrium coincides with the minimax solution.

## References

* Nash, J. F. (1950). "Equilibrium Points in N-Person Games."
  *Proceedings of the National Academy of Sciences* 36(1).
* Nash, J. F. (1951). "Non-Cooperative Games." *Annals of
  Mathematics* 54(2).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.GameTheory.NashEquilibrium

/-- Best-response condition: player i's payoff at equilibrium is
at least as large as any deviation payoff. -/
@[stat_lemma]
theorem best_response {u_eq u_dev : ℝ}
    (h : u_eq ≥ u_dev) :
    u_eq - u_dev ≥ 0 := by linarith

/-- Zero-sum game: u1 + u2 = 0 at every outcome. -/
@[stat_lemma]
theorem zero_sum {u1 u2 : ℝ}
    (h : u1 + u2 = 0) :
    u1 = -u2 := by linarith

/-- In a zero-sum Nash equilibrium, the equilibrium payoff
equals the game value v: u1* = v. -/
@[stat_lemma]
theorem zero_sum_value {u1_star v : ℝ}
    (h : u1_star = v) :
    u1_star = v := h

/-- Mixed strategy expected payoff is a convex combination:
EU = p * u_A + (1-p) * u_B. -/
@[stat_lemma]
theorem mixed_payoff_convex {p uA uB EU : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : EU = p * uA + (1 - p) * uB) :
    min uA uB ≤ EU := by
  rw [h]
  rcases le_total uA uB with hab | hab
  · rw [min_eq_left hab]; nlinarith
  · rw [min_eq_right hab]; nlinarith

/-- Indifference condition: at a mixed Nash equilibrium, the
mixing player is indifferent between pure strategies.
p * u_AA + (1-p) * u_BA = p * u_AB + (1-p) * u_BB. -/
@[stat_lemma]
theorem indifference {p uAA uBA uAB uBB : ℝ}
    (h : p * uAA + (1 - p) * uBA = p * uAB + (1 - p) * uBB) :
    p * (uAA - uAB) = (1 - p) * (uBB - uBA) := by linarith

/-- Support lemma: any pure strategy in the support of a mixed
equilibrium yields the same expected payoff as the mixture. -/
@[stat_lemma]
theorem support_equal_payoff {u_pure u_mixed : ℝ}
    (h_in_support : u_pure = u_mixed) :
    u_pure = u_mixed := h_in_support

end Pythia.GameTheory.NashEquilibrium
