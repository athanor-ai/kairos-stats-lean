/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Initial-State Correspondence for Miter Equivalence

Trust layer for cert tarballs (ATH-1109, item 2).

If the gold and gate registers are tied equal at cycle 0
(initial-state correspondence), then a miter circuit testing
output equivalence is a valid functional equivalence check.

## Statement

For gold G and gate T with identical initial states (or with
a register-tying map R : State_G → State_T such that
R(init_G) = init_T), the miter output at each cycle tests
whether the two designs agree on that cycle's output.

  init_G tied to init_T →
    miter_output(t) = (out_G(state_G(t)) ≠ out_T(state_T(t)))

So miter_output(t) = false for all t ≤ k ↔ output equivalence up to k.

## Status

Statement-only. Ships in cert tarball. Trivial once the circuit
model is formalized — the point is the explicit Lean statement
backing the cert claim.
-/
import Mathlib
import Pythia.Hardware.Equivalence.BMCSoundness

namespace Pythia.Hardware.Equivalence

variable {State Input Output : Type*} [DecidableEq Output]

structure MiterConfig (State Input Output : Type*) where
  gold : SequentialCircuit State Input Output
  gate : SequentialCircuit State Input Output
  init_tied : gold.init = gate.init

noncomputable def miterOutput (m : MiterConfig State Input Output) (trace : Fin n → Input) : Bool :=
  decide (m.gold.out (runCircuit m.gold trace) ≠ m.gate.out (runCircuit m.gate trace))

theorem miter_false_iff_equiv (m : MiterConfig State Input Output) (trace : Fin n → Input) :
    miterOutput m trace = false ↔
    m.gold.out (runCircuit m.gold trace) = m.gate.out (runCircuit m.gate trace) := by
  simp [miterOutput, decide_eq_false_iff_not, not_not]

theorem initial_state_correspondence
    (m : MiterConfig State Input Output)
    (k : ℕ)
    (h_miter_clear : ∀ n : ℕ, n ≤ k → ∀ trace : Fin n → Input,
      miterOutput m trace = false) :
    bmcEquiv m.gold m.gate k := by
  intro n hn trace
  exact (miter_false_iff_equiv m trace).mp (h_miter_clear n hn trace)

theorem tied_initial_implies_same_run
    (gold gate : SequentialCircuit State Input Output)
    (h_init : gold.init = gate.init)
    (h_next : gold.next = gate.next) :
    ∀ (n : ℕ) (trace : Fin n → Input),
      runCircuit gold trace = runCircuit gate trace := by
  intro n trace
  simp [runCircuit, h_init, h_next]

end Pythia.Hardware.Equivalence
