import Mathlib

-- Burch-Dill Refinement Maps for Pipelined Processors (1994).
-- THE foundational theorem of processor verification.
-- Formalized in ACL2, never in Lean. Until now.
--
-- Key idea: a pipelined processor is correct if there exists
-- a refinement map (abstraction function) from pipeline state
-- to architectural state such that:
--   abs(step_pipe(s)) = step_arch(abs(s))
-- after flushing the pipeline.

variable {ArchState PipeState Instr : Type*}

structure Processor (ArchState PipeState Instr : Type*) where
  arch_step : ArchState → Instr → ArchState
  pipe_step : PipeState → Instr → PipeState
  abs : PipeState → ArchState  -- abstraction function
  flush : PipeState → PipeState  -- flush pipeline to completion
  flush_idempotent : ∀ s, flush (flush s) = flush s

-- Burch-Dill commutative diagram:
-- After flushing, one pipeline step equals one architectural step
def burchDillCorrect (p : Processor ArchState PipeState Instr) : Prop :=
  ∀ (s : PipeState) (i : Instr),
    p.abs (p.flush (p.pipe_step s i)) = p.arch_step (p.abs (p.flush s)) i

/-
If Burch-Dill holds, n pipeline steps correspond to n architectural steps
-/
theorem burch_dill_n_steps (p : Processor ArchState PipeState Instr)
    (h : burchDillCorrect p)
    (instrs : List Instr) (s : PipeState) :
    p.abs (p.flush (instrs.foldl p.pipe_step s)) =
    instrs.foldl p.arch_step (p.abs (p.flush s)) := by
  induction' instrs using List.reverseRecOn with instrs ih generalizing s;
  · grind +locals;
  · simp_all +decide [ List.foldl_append ];
    rw [ ← ‹∀ s : PipeState, p.abs ( p.flush ( List.foldl p.pipe_step s instrs ) ) = List.foldl p.arch_step ( p.abs ( p.flush s ) ) instrs›, h ]

/-
Burch-Dill composition: if two pipeline stages are each correct,
the composed pipeline is correct.
Requires that the architectural model of the lower stage (p2) matches
the pipeline model of the upper stage (p1), i.e., p2.arch_step = p1.pipe_step.
-/
theorem burch_dill_compose
    {MidState : Type*}
    (p1 : Processor ArchState MidState Instr)
    (p2 : Processor MidState PipeState Instr)
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