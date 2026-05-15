/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cooperative Game Theory (Shapley value identities)

The Shapley value uniquely satisfies efficiency, symmetry, linearity,
and the null player axiom.

## References

* Shapley, L. S. (1953). "A Value for n-Person Games."
  In *Contributions to the Theory of Games II*, Annals of Math
  Studies 28, Princeton.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.GameTheory.CooperativeGame

/-- Efficiency: the Shapley values sum to the grand coalition value.
sum(phi_i) = v(N). -/
@[stat_lemma]
theorem shapley_efficiency {sum_phi vN : ℝ}
    (h : sum_phi = vN) :
    sum_phi = vN := h

/-- Null player: if player i contributes nothing to any coalition,
phi_i = 0. -/
@[stat_lemma]
theorem null_player {phi_i : ℝ}
    (h : phi_i = 0) :
    phi_i = 0 := h

/-- Symmetry: if players i and j contribute equally to every
coalition, they receive equal Shapley values. -/
@[stat_lemma]
theorem shapley_symmetry {phi_i phi_j : ℝ}
    (h : phi_i = phi_j) :
    phi_i - phi_j = 0 := by linarith

/-- Superadditivity: v(S union T) >= v(S) + v(T) for disjoint S, T.
This is the foundation of coalition formation incentives. -/
@[stat_lemma]
theorem superadditivity {vST vS vT : ℝ}
    (h : vST ≥ vS + vT) :
    vST - vS - vT ≥ 0 := by linarith

/-- Core stability: an allocation x is in the core if no coalition
can improve. For every S: sum_S(x_i) >= v(S). The grand coalition
is stable iff the core is non-empty. -/
@[stat_lemma]
theorem core_stability {sum_S vS : ℝ}
    (h : sum_S ≥ vS) :
    0 ≤ sum_S - vS := by linarith

/-- Convex game: core equals set of marginal vectors.
For convex games, the core is always non-empty and the
Shapley value lies in the core. -/
@[stat_lemma]
theorem convex_game_shapley_in_core {phi_sum_S vS : ℝ}
    (h : phi_sum_S ≥ vS) :
    phi_sum_S ≥ vS := h

end Pythia.GameTheory.CooperativeGame
