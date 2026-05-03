/-
Copyright (c) 2026 Pythia Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia

Pythia.Distributed.HappensBefore — Lamport happens-before and vector
clock causality theorems.

# Theorems

* `lamport_clock_happens_before` — The Lamport clock condition: if event
  e1 transitively happens-before e2 (in the sense that clocks are strictly
  increasing along the chain), then `clock e1 < clock e2`.

* `vector_clock_causality_completeness` — Soundness and completeness of
  vector clocks: `hb e1 e2 ↔` the vector-clock comparison holds, given
  the protocol invariants as hypotheses.

# References

Lamport, "Time, Clocks, and the Ordering of Events in a Distributed System",
  Communications of the ACM 21(7), 1978.
Mattern, "Virtual Time and Global States of Distributed Systems", 1989.
Fidge, "Timestamps in Message-Passing Systems", 1988.
-/
import Mathlib

namespace Pythia.Distributed

/-!
### lamport_clock_happens_before

The Lamport clock condition states that if e1 → e2 (happens-before), then
`clock e1 < clock e2`.  We model happens-before as `Relation.TransGen` of
the strict clock ordering, so the theorem is: transitivity of `<` on `ℕ`
is preserved through the transitive closure.  Proof by induction on
`Relation.TransGen`.
-/

/-- **Lamport clock happens-before** (ATH-940 §15, Lamport 1978):
the clock condition implies strict ordering along the happens-before chain. -/
theorem lamport_clock_happens_before
    {E : Type*}
    (clock : E → ℕ)
    (e1 e2 : E)
    (h : Relation.TransGen (fun e1' e2' => clock e1' < clock e2') e1 e2) :
    clock e1 < clock e2 := by
  induction h with
  | single hlt => exact hlt
  | tail _ hlt ih => exact Nat.lt_trans ih hlt

/-!
### vector_clock_causality_completeness

Vector clocks are both sound and complete for the happens-before relation,
given that the protocol maintains the two invariants (captured as
hypotheses `hVC_sound` and `hVC_complete`).  The iff proof reduces
immediately to the two hypotheses.
-/

/-- **Vector clock causality completeness** (ATH-940 §16, Mattern 1989 /
Fidge 1988): `hb e1 e2` iff the component-wise ≤ and strict-at-some-index
condition holds. -/
theorem vector_clock_causality_completeness
    {α E : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [DecidableEq E]
    (vc : E → α → ℕ)
    (hb : E → E → Prop)
    (hVC_sound : ∀ e1 e2, hb e1 e2 → ∀ p : α, vc e1 p ≤ vc e2 p ∧
        ∃ q : α, vc e1 q < vc e2 q)
    (hVC_complete : ∀ e1 e2,
        (∀ p : α, vc e1 p ≤ vc e2 p) ∧ (∃ q : α, vc e1 q < vc e2 q) →
        hb e1 e2)
    (e1 e2 : E) :
    hb e1 e2 ↔
    (∀ p : α, vc e1 p ≤ vc e2 p) ∧ (∃ q : α, vc e1 q < vc e2 q) := by
  constructor
  · intro h
    -- Pick any process index to extract the ∃ q witness from hVC_sound.
    have hsound : ∀ p : α, vc e1 p ≤ vc e2 p ∧ ∃ q : α, vc e1 q < vc e2 q :=
      hVC_sound e1 e2 h
    obtain ⟨p₀⟩ := (inferInstance : Nonempty α)
    exact ⟨fun p => (hsound p).1, (hsound p₀).2⟩
  · intro h
    exact hVC_complete e1 e2 h

end Pythia.Distributed
