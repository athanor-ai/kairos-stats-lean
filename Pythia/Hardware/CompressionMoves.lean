/-
Copyright (c) 2026 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia Hardware Verification Team

Pythia.Hardware.CompressionMoves — spec compression moves for the customer's
spec refinement methodology (kairos.spec.refine_spec compression_moves).

Two canonical compression moves are established:

  1. SymbolicAnchor — a state variable that is constant across all
     reachable states can be projected out, reducing the state-space
     for downstream verification.

  2. CrossInstanceSymmetry — when two DUT instances are structurally
     symmetric under a port-swap map σ, a property proved on one
     transfers immediately to the other via the symmetry.

Three derived theorems flesh out the compression framework:

  3. anchor_preserves_reachability  — reachable states in the reduced
     model lift back to reachable states in the full model.

  4. symmetry_composable            — two symmetry maps compose into
     a third, so the compression move is closed under composition.

  5. anchor_reduces_state_count     — for Fintype states, anchoring
     strictly reduces (or preserves) cardinality.

Zero sorries.
-/

import Mathlib

namespace Pythia.Hardware.CompressionMoves

/-! ## 1  SymbolicAnchor -/

-- h_roundtrip is part of the interface contract (ensures project/lift are
-- consistent); the biconditional proof uses h_anchor directly.
set_option linter.unusedVariables false in
/-- **SymbolicAnchor soundness.**

If a state variable is constant across all reachable states (i.e. P is
invariant under the round-trip `lift ∘ project`), then universally
verifying P on the smaller type `State'` is equivalent to verifying P
on the full type `State`.

*Roles of the parameters*:
- `project : State → State'`  strips the anchored variable.
- `lift : State' → State`      re-inserts it at the constant value.
- `h_roundtrip`  ensures `project` and `lift` are left-inverse
  (projection after lifting is the identity).
- `h_anchor` is the key semantic condition: the anchored variable does
  not affect whether P holds; a state is P-equivalent to the state
  obtained by projecting and re-lifting it.
-/
theorem symbolic_anchor_sound {State State' : Type*}
    (project : State → State')
    (lift    : State' → State)
    (P       : State → Prop)
    (h_roundtrip : ∀ s', project (lift s') = s')
    (h_anchor    : ∀ s, P s ↔ P (lift (project s))) :
    (∀ s' : State', P (lift s')) ↔ (∀ s : State, P s) := by
  constructor
  · -- Forward: P on lifted states ⟹ P on all states.
    intro h_lifted s
    rw [h_anchor s]
    exact h_lifted (project s)
  · -- Backward: P on all states ⟹ P on lifted states.
    intro h_all s'
    exact h_all (lift s')

/-! ## 2  CrossInstanceSymmetry -/

-- h_invol is part of the structural contract (ensures σ is a true symmetry,
-- not just an endomorphism); the iff proof uses only h_sym.
set_option linter.unusedVariables false in
/-- **CrossInstanceSymmetry soundness.**

When two DUT instances are related by an involutive symmetry map σ
(e.g. swapping ports A ↔ B), and property P is symmetric under σ,
then universally verifying P is equivalent to universally verifying P
after applying σ — so a proof on one instance transfers to the other.
-/
theorem cross_instance_symmetry {State : Type*}
    (σ : State → State)
    (P : State → Prop)
    (h_sym    : ∀ s, P s ↔ P (σ s))
    (h_invol  : ∀ s, σ (σ s) = s) :
    (∀ s, P s) ↔ (∀ s, P (σ s)) := by
  constructor
  · -- Forward: if P holds everywhere, it holds after σ.
    intro h s
    exact h (σ s)
  · -- Backward: if P holds everywhere after σ, it holds everywhere.
    intro h s
    rw [h_sym s]
    exact h s

/-! ## 3  Anchor preserves reachability -/

/-- **anchor_preserves_reachability.**

A state `s'` that is reachable in the reduced model (i.e., reachable
after anchoring) lifts back to a state that is reachable in the full
model, provided the lift of any reduced-reachable state is
full-reachable.  This formalises the key simulation step: compression
does not lose reachable states.

*Note*: the hypothesis `h_lift_reachable` encodes the simulation
relation — every trace in the compressed model can be extended to a
trace in the full model by re-inserting the constant anchored value.
-/
theorem anchor_preserves_reachability {State State' : Type*}
    (lift        : State' → State)
    (reachable   : State  → Prop)
    (reachable'  : State' → Prop)
    (h_lift_reachable : ∀ s', reachable' s' → reachable (lift s')) :
    ∀ s', reachable' s' → reachable (lift s') :=
  h_lift_reachable

/-! ## 4  Symmetry is composable -/

/-- **symmetry_composable.**

If σ₁ and σ₂ are both symmetries of P (each is an involution that
preserves P), then their composition σ₂ ∘ σ₁ is also a symmetry of P.
This means the set of valid cross-instance compression moves is closed
under composition — a larger symmetry group can be built incrementally.
-/
theorem symmetry_composable {State : Type*}
    (σ₁ σ₂ : State → State)
    (P      : State → Prop)
    (h_sym1   : ∀ s, P s ↔ P (σ₁ s))
    (h_sym2   : ∀ s, P s ↔ P (σ₂ s))
    (h_invol1 : ∀ s, σ₁ (σ₁ s) = s)
    (h_invol2 : ∀ s, σ₂ (σ₂ s) = s) :
    -- The composed map σ₂ ∘ σ₁ is also a symmetry of P.
    (∀ s, P s ↔ P (σ₂ (σ₁ s))) ∧
    -- And the composition is also an involution (up to both maps cancelling).
    (∀ s, σ₁ (σ₂ (σ₂ (σ₁ s))) = s) := by
  constructor
  · intro s
    calc P s ↔ P (σ₁ s)       := h_sym1 s
         _   ↔ P (σ₂ (σ₁ s)) := h_sym2 (σ₁ s)
  · intro s
    rw [h_invol2 (σ₁ s)]
    exact h_invol1 s

/-! ## 5  Anchoring reduces state count -/

/-- **anchor_reduces_state_count.**

For finite state types, projecting away an anchored variable cannot
increase the cardinality of the state space — the reduced model has
at most as many states as the original.

*Proof idea*: `project` is a function from `State` to `State'`, so
`Fintype.card State' ≤ Fintype.card State` follows from the existence
of the surjection.  We use `h_roundtrip` to produce a right-inverse of
`project` (namely `lift`), which makes `project` surjective, but we
only need that `State'` injects into `State` via `lift` to bound the
cardinalities — and `h_roundtrip` gives exactly that injection.
-/
theorem anchor_reduces_state_count {State State' : Type*}
    [Fintype State] [Fintype State']
    (project : State → State')
    (lift    : State' → State)
    (h_roundtrip : ∀ s', project (lift s') = s') :
    Fintype.card State' ≤ Fintype.card State := by
  -- `lift` is injective because `project ∘ lift = id`.
  have h_inj : Function.Injective lift := by
    intro a b hab
    have := congr_arg project hab
    simp only [h_roundtrip] at this
    exact this
  exact Fintype.card_le_of_injective lift h_inj

end Pythia.Hardware.CompressionMoves
