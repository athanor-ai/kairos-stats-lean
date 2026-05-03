/-
  Pythia.Networking.BellmanFord
  Bellman-Ford distance estimates are non-negative when edge weights
  and initial distances are non-negative.

  Bellman 1958; Ford and Fulkerson 1962. In the Bellman-Ford shortest-path
  algorithm, relaxation preserves non-negativity of distance estimates
  whenever edge weights are non-negative. We prove this by structural
  induction on the number of relaxation rounds, parameterised over an
  abstract relax function that is assumed to preserve non-negativity.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Pythia.Networking.BellmanFord

/-- After n rounds of Bellman-Ford relaxation, every distance estimate
    remains non-negative, given non-negative edge weights and initial
    distances. The relax function is abstract; the hypothesis
    h_relax_preserves encodes that relaxation respects non-negativity. -/
theorem bellman_ford_distance_nonneg
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (weight : V → V → Option ℝ)
    (h_nonneg_weights : ∀ u v w, weight u v = some w → 0 ≤ w)
    (d : V → ℝ) (h_init : ∀ v, 0 ≤ d v)
    (relax : (V → ℝ) → (V → ℝ))
    (h_relax_preserves : ∀ d', (∀ v, 0 ≤ d' v) → ∀ v, 0 ≤ relax d' v)
    (n : ℕ) (u : V) :
    0 ≤ (Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') n) u := by
  suffices h : ∀ v, 0 ≤ (Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') n) v
    from h u
  induction n with
  | zero => exact h_init
  | succ k ih => exact h_relax_preserves _ ih

end Pythia.Networking.BellmanFord
