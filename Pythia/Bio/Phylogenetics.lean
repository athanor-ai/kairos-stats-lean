/-
Pythia.Bio.Phylogenetics — phylogenetic likelihood + Felsenstein's
algorithm.

A phylogeny is specified by a rooted binary tree with leaf-labels
(extant species) and edge lengths (evolutionary time). A substitution
model assigns a transition matrix `P(t)` to each edge of length `t`.
Felsenstein's algorithm (1981) computes the likelihood of observed
leaf states under the substitution model in `O(n)` traversals via
dynamic programming up the tree.

Mathlib has nothing on phylogenetics. This module ships the
foundational scaffold; precise algorithm correctness statement is
queued to Aristotle (item 41).

## Status

Scaffold. Full Felsenstein correctness proof (tree-induction over
post-order traversal) is queued to Aristotle.
-/
import Mathlib

namespace Pythia.Bio.Phylogenetics

/-- A simple binary tree with edge-lengths and leaf-labels of type α. -/
inductive BinaryTree (α : Type) where
  | leaf (label : α) : BinaryTree α
  | node (edgeLen : ℝ) (left right : BinaryTree α) : BinaryTree α
  deriving Inhabited

/-- A substitution model on a finite set of states `State`: continuous
Markov chain with transition matrix `P(t) = exp(t * Q)` for rate
matrix `Q`. -/
structure SubstitutionModel (State : Type) [Fintype State] [DecidableEq State] where
  pi : State → ℝ
  pi_nonneg : ∀ s, 0 ≤ pi s
  pi_sum : ∑ s : State, pi s = 1
  P : ℝ → State → State → ℝ
  P_nonneg : ∀ t s s', 0 ≤ t → 0 ≤ P t s s'
  P_row_sum : ∀ t s, 0 ≤ t → ∑ s' : State, P t s s' = 1
  reversible : ∀ t s s', 0 ≤ t → pi s * P t s s' = pi s' * P t s' s

/-- Felsenstein correctness specification (Aristotle queue 41). -/
theorem felsenstein_correct_spec : True := by trivial

/-- Jukes-Cantor 1969: 4-state DNA model. Equilibrium uniform 1/4.
Transition: P(s → s) = 1/4 + (3/4) exp(-4 α t); P(s → s') = 1/4 - 1/4 exp(-4 α t). -/
noncomputable def JukesCantor_pi : Fin 4 → ℝ := fun _ => 1 / 4

noncomputable def JukesCantor_P (α : ℝ) : ℝ → Fin 4 → Fin 4 → ℝ := fun t s s' =>
  if s = s' then
    1/4 + (3/4) * Real.exp (-4 * α * t)
  else
    1/4 - (1/4) * Real.exp (-4 * α * t)

theorem JukesCantor_pi_sum : ∑ s : Fin 4, JukesCantor_pi s = 1 := by
  simp [JukesCantor_pi, Fin.sum_univ_four]

end Pythia.Bio.Phylogenetics
