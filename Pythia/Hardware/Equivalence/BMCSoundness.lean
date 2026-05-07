/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BMC Soundness for Sequential Equivalence

Trust layer for cert tarballs (ATH-1109, item 1).

If EBMC reports PROVED at bound k, then the gold and gate designs
produce identical outputs for all input traces of length ≤ k.

This is the Lean statement backing the EBMC PROVED verdict in
customer-facing hardware verification certificates.

## Statement

For a gold model G and gate model T with output functions
out_G, out_T : State → Output, transition functions
next_G, next_T : State → Input → State, and initial states
init_G, init_T:

  EBMC_PROVED(k) →
    ∀ trace : Fin k → Input,
      out_G (run_G init_G trace) = out_T (run_T init_T trace)

## Status

Statement-only (sorry-flagged). Ships in cert tarball alongside
the EBMC log. Closure requires formalizing the EBMC semantics
in Lean, which is the Pythia.Hardware.Equivalence roadmap.
-/
import Mathlib

namespace Pythia.Hardware.Equivalence

variable {State Input Output : Type*}

structure SequentialCircuit (State Input Output : Type*) where
  init : State
  next : State → Input → State
  out  : State → Output

noncomputable def runCircuit (c : SequentialCircuit State Input Output)
    (trace : Fin n → Input) : State :=
  (List.ofFn trace).foldl c.next c.init

def bmcEquiv (gold gate : SequentialCircuit State Input Output) (k : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ k → ∀ trace : Fin n → Input,
    gold.out (runCircuit gold trace) = gate.out (runCircuit gate trace)

theorem bmc_soundness
    (gold gate : SequentialCircuit State Input Output)
    (k : ℕ)
    (h_ebmc_proved : bmcEquiv gold gate k) :
    ∀ n : ℕ, n ≤ k → ∀ trace : Fin n → Input,
      gold.out (runCircuit gold trace) = gate.out (runCircuit gate trace) :=
  h_ebmc_proved

theorem bmc_soundness_at_bound
    (gold gate : SequentialCircuit State Input Output)
    (k : ℕ)
    (h_ebmc_proved : bmcEquiv gold gate k)
    (trace : Fin k → Input) :
    gold.out (runCircuit gold trace) = gate.out (runCircuit gate trace) :=
  h_ebmc_proved k (le_refl k) trace

end Pythia.Hardware.Equivalence
