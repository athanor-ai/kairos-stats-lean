/-
  Pythia.Networking.SplitHorizon
  Split-horizon eliminates count-to-infinity on loop-free topologies.

  RFC 1058 §2.2.3: on a loop-free topology with n vertices,
  Bellman-Ford distance-vector iterations converge within n steps and
  remain stable thereafter.  We capture the essential algebraic core:
  if the relax operator is idempotent after n_vertices steps (modelling
  split-horizon's prevention of routing loops), then distance vectors
  stabilize at or before step n_vertices and stay fixed for all future
  steps.

  Parametrized form: the relax_step function is abstract; the hypothesis
  h_idempotent_after_n encodes that one additional step after n_vertices
  does not change the result, and we propagate this by induction on the
  remaining steps.

  Deviation from spec: explicit `motive := fun _ => V → ℝ` annotations are
  required on all Nat.recAux occurrences (including in the hypothesis) to
  allow elaboration.  The statement is otherwise identical to the spec.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

set_option linter.unusedVariables false

namespace Pythia.Networking.SplitHorizon

/-- Unfolding lemma: one more step of Nat.recAux equals one application of relax. -/
private theorem recAux_succ {V : Type*}
    (relax : (V → ℝ) → (V → ℝ)) (d : V → ℝ) (n : ℕ) :
    Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') (n + 1) =
    relax (Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') n) := rfl

/-- Helper: if the iterate is stable at step k (one additional step yields the
    same result), then it is stable at all steps k + m. Proof by induction on m. -/
private theorem recAux_stable {V : Type*}
    (relax : (V → ℝ) → (V → ℝ)) (d : V → ℝ) (k : ℕ)
    (h_idem : Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') (k + 1) =
              Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') k) :
    ∀ m : ℕ,
      Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') (k + m) =
      Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax d') k := by
  intro m
  induction m with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_succ, recAux_succ, ih]
      rw [recAux_succ] at h_idem
      exact h_idem

/-- Split-horizon convergence theorem.
    On a loop-free n-vertex topology, if applying the relax operator one
    additional time after n_vertices steps produces no change (the split-horizon
    invariant), then distance vectors are stable from step n_vertices onward:
    there exists T ≤ n_vertices such that the iterate is fixed for all t ≥ T. -/
theorem split_horizon_no_count_to_infinity
    {V : Type*} [Fintype V]
    (n_vertices : ℕ) (h_card : Fintype.card V = n_vertices)
    (relax_step : (V → ℝ) → (V → ℝ))
    (h_idempotent_after_n : ∀ d : V → ℝ,
      Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax_step d') (n_vertices + 1) =
      Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax_step d') n_vertices)
    (d : V → ℝ) :
    ∃ T : ℕ, T ≤ n_vertices ∧
      ∀ t : ℕ, t ≥ T →
        Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax_step d') t =
        Nat.recAux (motive := fun _ => V → ℝ) d (fun _ d' => relax_step d') T := by
  use n_vertices
  refine ⟨le_refl _, ?_⟩
  intro t ht
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact recAux_stable relax_step d n_vertices (h_idempotent_after_n d) m

end Pythia.Networking.SplitHorizon
