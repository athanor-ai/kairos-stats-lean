/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Verification.Foundations.Refinement

Refinement-map correctness for pipelined / staged processors, after
Burch & Dill (CAV 1994) — *Automatic verification of pipelined
microprocessor control*. THE foundational theorem of processor
verification. Formalized in ACL2 (Hunt, Russinoff, Kaufmann) for
decades; this is the Lean 4 / Mathlib lift.

Key idea: a pipelined processor is correct if there exists a refinement
map (abstraction function) from pipeline state to architectural state
such that, after flushing the pipeline,

    abs (step_pipe s) = step_arch (abs s).

This module is part of the **4+1 universal invariant set** that the
customer-facing `flow_guard` preflight gate cites.

## Naming note (2026-05-13)

Type variables renamed `{ArchState PipeState Instr : Type*}` →
`{S P I : Type*}` per the signature audit: in the original private file
`ArchState` was a polymorphic type variable, but a *different* file in
the same module (`Pythia.Hardware.RefinementComposition`) defined a
concrete struct `ArchState n := { gpr : Fin n → ℤ }`. The two
unrelated symbols sharing a name produced a misleading-name collision
flagged by asabi. The polymorphic version retains the original
mathematical content; only the bound variable names changed.

Theorems renamed `burch_dill_n_steps → refinement_n_steps` and
`burch_dill_compose → refinement_compose` so the public surface uses
the domain-neutral noun. The Burch-Dill provenance is preserved in
this docstring and in the private re-export shim.
-/

import Mathlib

namespace Pythia.Verification.Foundations.Refinement

variable {S P I : Type*}

/-- A *processor* over architectural state `S`, pipeline state `P`, and
instruction type `I`. Captures one step of the architectural model,
one step of the pipelined model, an abstraction function from pipeline
to architecture, and a `flush` operation that drains the pipeline to a
state on which the abstraction is observable. -/
structure Processor (S P I : Type*) where
  arch_step : S → I → S
  pipe_step : P → I → P
  /-- Abstraction function: pipeline state to architectural state. -/
  abs : P → S
  /-- Drain the pipeline to a state on which `abs` agrees with the
      architectural model. -/
  flush : P → P
  flush_idempotent : ∀ s, flush (flush s) = flush s

/-- **Burch-Dill commutative diagram.** After flushing, one pipeline
step equals one architectural step. -/
def burchDillCorrect (p : Processor S P I) : Prop :=
  ∀ (s : P) (i : I),
    p.abs (p.flush (p.pipe_step s i)) = p.arch_step (p.abs (p.flush s)) i

/-- **Refinement over `n` steps.** If the Burch-Dill commutative
diagram holds for one step, it holds for any finite instruction
sequence: `n` pipeline steps correspond to `n` architectural steps
after flushing.

    Note. Formerly `Pythia.Hardware.burch_dill_n_steps`. -/
theorem refinement_n_steps (p : Processor S P I)
    (h : burchDillCorrect p)
    (instrs : List I) (s : P) :
    p.abs (p.flush (instrs.foldl p.pipe_step s)) =
    instrs.foldl p.arch_step (p.abs (p.flush s)) := by
  induction' instrs using List.reverseRecOn with instrs ih generalizing s;
  · grind +locals;
  · simp_all +decide [ List.foldl_append ];
    rw [ ← ‹∀ s : P, p.abs ( p.flush ( List.foldl p.pipe_step s instrs ) ) = List.foldl p.arch_step ( p.abs ( p.flush s ) ) instrs›, h ]

/-- **Refinement composition.** If two pipeline stages are each
Burch-Dill correct, the composed pipeline is correct. Requires that
the architectural model of the lower stage `p2` matches the pipeline
model of the upper stage `p1`, i.e., `p2.arch_step = p1.pipe_step`.

    Note. Formerly `Pythia.Hardware.burch_dill_compose`. -/
theorem refinement_compose
    {MidState : Type*}
    (p1 : Processor S MidState I)
    (p2 : Processor MidState P I)
    (h_compat : p2.arch_step = p1.pipe_step)
    (h1 : burchDillCorrect p1) (h2 : burchDillCorrect p2) :
    burchDillCorrect {
      arch_step := p1.arch_step
      pipe_step := p2.pipe_step
      abs := fun s => p1.abs (p1.flush (p2.abs s))
      flush := fun s => p2.flush s
      flush_idempotent := p2.flush_idempotent
    } := by
  intro s i; have := h1 ( p2.abs s ) i; have := h2 s i; aesop;

end Pythia.Verification.Foundations.Refinement
