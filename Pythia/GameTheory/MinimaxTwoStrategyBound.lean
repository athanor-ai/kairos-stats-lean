/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weak minimax inequality for a 2x2 payoff matrix

For any 2x2 real payoff matrix `A : Fin 2 → Fin 2 → ℝ` (row player
chooses `i`, column player chooses `j`, entry `A i j` is the row
player's payoff), the maximin value is bounded above by the
minimax value:

    max_i min_j A i j  ≤  min_j max_i A i j.

This is the discrete weak minimax inequality, true for any finite
game without any mixed-strategy or convexity assumptions. The
strong-equality minimax theorem (von Neumann 1928) requires mixed
strategies; this lemma is the pure-strategy upper-bound that holds
unconditionally.

## Main results

* `minimax_two_strategy_bound` — `max_i min_j A i j ≤ min_j max_i A i j`
  for any `A : Fin 2 → Fin 2 → ℝ`.

## Why this lemma

Mathlib has `Finset.sup_inf_le_inf_sup` for general lattices but
no named pure-strategy minimax inequality in the game-theory
flavor. Pythia exposes the 2x2 specialization so the `pythia`
cascade closes finite-game weak-minimax goals by name.

## References

* von Neumann, J. "Zur Theorie der Gesellschaftsspiele."
  Mathematische Annalen 100: 295-320 (1928).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.GameTheory

/-- **Weak minimax inequality (2x2 case).** For any 2x2 real payoff
matrix `A`, `max_i min_j A i j ≤ min_j max_i A i j`. The proof
decomposes the outer `max ≤ min` into four `min_? ≤ max_?` chains,
each closed by `min_le_left/right` then `le_max_left/right` via
`le_trans`. -/
@[stat_lemma]
theorem minimax_two_strategy_bound (A : Fin 2 → Fin 2 → ℝ) :
    max (min (A 0 0) (A 0 1)) (min (A 1 0) (A 1 1)) ≤
      min (max (A 0 0) (A 1 0)) (max (A 0 1) (A 1 1)) := by
  -- Each of `min (A i 0) (A i 1)` is bounded above by every entry
  -- of column 0 or column 1 (via `min_le_left/right`), which is in
  -- turn bounded above by `max (A 0 j) (A 1 j)` (via
  -- `le_max_left/right`). Four `le_trans` chains close the goal.
  have h00 : min (A 0 0) (A 0 1) ≤ max (A 0 0) (A 1 0) :=
    le_trans (min_le_left _ _) (le_max_left _ _)
  have h01 : min (A 0 0) (A 0 1) ≤ max (A 0 1) (A 1 1) :=
    le_trans (min_le_right _ _) (le_max_left _ _)
  have h10 : min (A 1 0) (A 1 1) ≤ max (A 0 0) (A 1 0) :=
    le_trans (min_le_left _ _) (le_max_right _ _)
  have h11 : min (A 1 0) (A 1 1) ≤ max (A 0 1) (A 1 1) :=
    le_trans (min_le_right _ _) (le_max_right _ _)
  exact le_min (max_le h00 h10) (max_le h01 h11)

end Pythia.GameTheory
