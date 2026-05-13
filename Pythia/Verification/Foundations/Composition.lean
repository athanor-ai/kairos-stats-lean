/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Verification.Foundations.Composition

Polymorphic schema for compositional refinement.

Originally `Pythia.Hardware.RefinementComposition.ncs_composition`,
which baked in `ArchState n := {gpr : Fin n → ℤ}` and an
arithmetic-specific consistency relation. The hardware specialization
stays private (lives in `Pythia.Hardware.RefinementComposition` as an
instance of the schema below); the schema is published here so
`flow_guard` and customer surfaces can cite it without leaking
hardware specifics.

This module is part of the **4+1 universal invariant set** that the
customer-facing `flow_guard` preflight gate cites.

Domain-specific consistency notions (arithmetic, control-flow,
memory ordering) each become instances of this schema by discharging
the `IsConsistency` predicate at the appropriate relation.
-/

import Mathlib

namespace Pythia.Verification.Foundations.Composition

variable {State Instr : Type*}

/-- Two implementations *refine* each other when they produce the same
    final state for every input sequence. The direction is
    weak-refinement-via-equality. -/
def refines (implA implB : List Instr → State) : Prop :=
  ∀ instrs : List Instr, implA instrs = implB instrs

/-- A binary relation `R` between implementations is a *consistency
    relation* when it implies trace-equality. Domain-specific
    consistency notions (arithmetic, control-flow, memory ordering)
    each become instances of this schema. -/
def IsConsistency
    (R : (List Instr → State) → (List Instr → State) → Prop) : Prop :=
  ∀ implA implB, R implA implB → refines implA implB

/-- **Compositional refinement schema.** Any domain-specific
    consistency relation that satisfies `IsConsistency` yields
    refinement. The hardware-specific `arithmeticConsistent`
    instantiation lives in `Pythia.Hardware.RefinementComposition`
    and discharges `IsConsistency arithmeticConsistent` separately. -/
theorem refinement_composition
    {R : (List Instr → State) → (List Instr → State) → Prop}
    (hR : IsConsistency R)
    {implA implB : List Instr → State}
    (h : R implA implB) :
    refines implA implB :=
  hR implA implB h

end Pythia.Verification.Foundations.Composition
