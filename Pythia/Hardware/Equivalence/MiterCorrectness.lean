/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Miter Circuit Correctness

Trust layer for cert tarballs (ATH-1109, item 3).

A miter circuit XORs the outputs of a gold design G and a gate design T.
A true miter output at cycle t is a witness that G and T diverge at t.
Conversely, if the miter is false for every trace of length ≤ k, the two
designs are output-equivalent up to k cycles (`bmcEquiv`).

## Theorems

1. `miter_detects_divergence` — divergent outputs imply true (nonzero) miter.
2. `miter_all_zero_implies_equiv` — all-false miter up to k implies `bmcEquiv k`.
3. `sequential_equivalence_under_initial` — identical init, next, and out
   imply output agreement on all traces (unbounded).
4. `bridge_invariant_soundness` — given an invariant I maintained at every
   step of the trace, I implies output equality for that trace.
   `bridge_invariant_soundness_inductive` — stronger: if I is inductive
   (held at init, preserved by each transition), outputs agree on all traces.

## Status

Sorry-free. All proofs close by elementary term manipulation and list-foldl
induction; no auxiliary axioms beyond Mathlib.
-/
import Mathlib
import Pythia.Hardware.Equivalence.BMCSoundness

set_option linter.unusedSectionVars false

namespace Pythia.Hardware.Equivalence

variable {State Input Output : Type*} [DecidableEq Output]

/-! ## Miter XOR output -/

/-- The Boolean miter output for a single trace: `true` iff the gold and
gate outputs differ on that trace.  This is the single-bit XOR that a
standard miter circuit drives to indicate a counterexample. -/
noncomputable def miterXOR
    (gold gate : SequentialCircuit State Input Output)
    (trace : Fin n → Input) : Bool :=
  decide (gold.out (runCircuit gold trace) ≠ gate.out (runCircuit gate trace))

/-- The miter output is `true` iff the outputs differ. -/
theorem miterXOR_iff
    (gold gate : SequentialCircuit State Input Output)
    (trace : Fin n → Input) :
    miterXOR gold gate trace = true ↔
    gold.out (runCircuit gold trace) ≠ gate.out (runCircuit gate trace) := by
  simp [miterXOR]

/-- The miter output is `false` iff the outputs agree. -/
theorem miterXOR_false_iff
    (gold gate : SequentialCircuit State Input Output)
    (trace : Fin n → Input) :
    miterXOR gold gate trace = false ↔
    gold.out (runCircuit gold trace) = gate.out (runCircuit gate trace) := by
  simp [miterXOR]

/-! ## Theorem 1 : miter_detects_divergence -/

/-- **Miter detects divergence.**
If the gold and gate circuits produce different outputs on some input trace,
the miter XOR output is `true` (nonzero) on that trace.  This is the
soundness direction: a true miter output is always a genuine counterexample. -/
theorem miter_detects_divergence
    (gold gate : SequentialCircuit State Input Output)
    (n : ℕ)
    (trace : Fin n → Input)
    (h_diff : gold.out (runCircuit gold trace) ≠
              gate.out (runCircuit gate trace)) :
    miterXOR gold gate trace = true :=
  (miterXOR_iff gold gate trace).mpr h_diff

/-! ## Theorem 2 : miter_all_zero_implies_equiv -/

/-- **All-zero miter implies bounded equivalence.**
If the miter output is `false` for every input trace of length at most `k`,
then `bmcEquiv gold gate k` holds: the two designs are output-equivalent at
every cycle up to bound `k`. -/
theorem miter_all_zero_implies_equiv
    (gold gate : SequentialCircuit State Input Output)
    (k : ℕ)
    (h_zero : ∀ n : ℕ, n ≤ k → ∀ trace : Fin n → Input,
      miterXOR gold gate trace = false) :
    bmcEquiv gold gate k := by
  intro n hn trace
  exact (miterXOR_false_iff gold gate trace).mp (h_zero n hn trace)

/-- Converse: bounded equivalence implies all-zero miter up to the bound. -/
theorem equiv_implies_miter_all_zero
    (gold gate : SequentialCircuit State Input Output)
    (k : ℕ)
    (h_equiv : bmcEquiv gold gate k) :
    ∀ n : ℕ, n ≤ k → ∀ trace : Fin n → Input,
      miterXOR gold gate trace = false := by
  intro n hn trace
  exact (miterXOR_false_iff gold gate trace).mpr (h_equiv n hn trace)

/-! ## Theorem 3 : sequential_equivalence_under_initial -/

/-- **Sequential equivalence under identical structure.**
If gold and gate share the same initial state, transition function, and
output function, they produce identical outputs on every input trace
(with no bound on trace length).

Note: all three fields must agree.  Sharing only `init` and `next`
guarantees the same run-state but not the same output if the output
functions differ; sharing only `init` and `out` is insufficient because
the states can diverge after the first step. -/
theorem sequential_equivalence_under_initial
    (gold gate : SequentialCircuit State Input Output)
    (h_init : gold.init = gate.init)
    (h_next : gold.next = gate.next)
    (h_out  : gold.out  = gate.out) :
    ∀ (n : ℕ) (trace : Fin n → Input),
      gold.out (runCircuit gold trace) = gate.out (runCircuit gate trace) := by
  intro n trace
  have h_run : runCircuit gold trace = runCircuit gate trace := by
    simp [runCircuit, h_init, h_next]
  simp [h_run, h_out]

/-- Corollary: structurally identical designs satisfy `bmcEquiv` at every
bound, and hence at all trace lengths. -/
theorem sequential_equiv_bmcEquiv_all_k
    (gold gate : SequentialCircuit State Input Output)
    (h_init : gold.init = gate.init)
    (h_next : gold.next = gate.next)
    (h_out  : gold.out  = gate.out)
    (k : ℕ) :
    bmcEquiv gold gate k := by
  intro n _hn trace
  exact sequential_equivalence_under_initial gold gate h_init h_next h_out n trace

/-! ## Theorem 4 : bridge_invariant_soundness -/

/-- Internal helper: a list-foldl with two transition functions preserves
a relation `I` when each individual step preserves it. -/
private lemma foldl_invariant
    {S1 S2 : Type*}
    (I : S1 → S2 → Prop)
    (f1 : S1 → Input → S1)
    (f2 : S2 → Input → S2)
    (h_pres : ∀ s1 s2 i, I s1 s2 → I (f1 s1 i) (f2 s2 i))
    (s1₀ : S1) (s2₀ : S2)
    (h_start : I s1₀ s2₀)
    (inputs : List Input) :
    I (inputs.foldl f1 s1₀) (inputs.foldl f2 s2₀) := by
  induction inputs generalizing s1₀ s2₀ with
  | nil => simpa
  | cons a as ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (h_pres _ _ _ h_start)

set_option linter.unusedVariables false in
/-- **Bridge invariant soundness (externally maintained).**
Let `I : State → State → Prop` be a relation on (gold-state, gate-state)
pairs.  If `I` implies output equality and `I` holds at the final states of
a particular run (as witnessed by `h_maintained`), then outputs agree on
that run.

This is the "shallow" form: the caller supplies evidence that `I` holds
at the run's terminal state.  Use `bridge_invariant_soundness_inductive`
when `I` is proven inductive (held at init, preserved by every step). -/
theorem bridge_invariant_soundness
    (gold gate : SequentialCircuit State Input Output)
    (I : State → State → Prop)
    (h_out : ∀ sg sg' : State, I sg sg' → gold.out sg = gate.out sg') :
    ∀ (n : ℕ) (trace : Fin n → Input)
      (h_maintained : I (runCircuit gold trace) (runCircuit gate trace)),
      gold.out (runCircuit gold trace) = gate.out (runCircuit gate trace) := by
  intro n trace hmaint
  exact h_out _ _ hmaint

/-- **Bridge invariant soundness (fully inductive).**
If:
* `h_init` — invariant `I` holds at the joint initial state pair,
* `h_pres` — every single transition of gold paired with the corresponding
  gate transition preserves `I`,
* `h_out`  — whenever `I` holds at a state pair, the outputs agree,

then gold and gate produce identical outputs on **all** input traces,
without any bound on trace length.

The proof establishes `I (runCircuit gold trace) (runCircuit gate trace)` by
list-foldl induction via `foldl_invariant`, then applies `h_out`. -/
theorem bridge_invariant_soundness_inductive
    (gold gate : SequentialCircuit State Input Output)
    (I : State → State → Prop)
    (h_init : I gold.init gate.init)
    (h_pres : ∀ (sg sg' : State) (inp : Input),
      I sg sg' → I (gold.next sg inp) (gate.next sg' inp))
    (h_out  : ∀ sg sg' : State, I sg sg' → gold.out sg = gate.out sg') :
    ∀ (n : ℕ) (trace : Fin n → Input),
      gold.out (runCircuit gold trace) = gate.out (runCircuit gate trace) := by
  intro n trace
  simp only [runCircuit]
  apply h_out
  exact foldl_invariant I gold.next gate.next h_pres _ _ h_init (List.ofFn trace)

end Pythia.Hardware.Equivalence
