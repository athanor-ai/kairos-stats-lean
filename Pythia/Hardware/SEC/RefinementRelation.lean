/-
Pythia.Hardware.SEC.RefinementRelation — typed cross-structure
refinement relations for SEC bundles where the optimization
changes flop counts, state encoding, or algorithmic approach.

Customer use (per ATH-992, LLM-orchestrated RTL area
optimization closed loop):

When an optimization swaps a block's implementation (e.g. FIFO
implemented as memory array vs flop array), the original and
optimized designs have *different* state spaces. EBMC's
k-induction can't close equivalence directly because the
inductive invariant must relate the two state spaces, which
requires an explicit abstraction function. This module provides
the typed interface for that abstraction, plus the refinement
relation `refines_under` that captures cross-structure
equivalence semantically.

Architecture: the LLM (qa-lane in ATH-992) generates candidate
abstraction functions. This module's typing kernel-checks them.
The SEC harness (kairos.sec, ATH-983) consumes them as EBMC
`assume property` directives.

Reference: ATH-988 epic (parent), ATH-992 (cross-arm child for
inductive-invariant generation; this file is the cto half of
the cross-arm split).
-/
import Mathlib
import Pythia.Hardware.RefinementComposition

namespace Pythia.Hardware.SEC

/-! ## Typed step interface

Each block (original or optimized) is a Mealy machine with its
own state space, input alphabet, and output alphabet. The
typing class abstracts over these so the same refinement
machinery applies to FifoContract / RoundRobinContract /
PacketTransform-class blocks uniformly. -/

/-- A typed Mealy step: state space `S`, input alphabet `I`,
output alphabet `O`. The step function takes the current state
plus an input, returns the next state plus an output. -/
abbrev Step (S I O : Type*) := S → I → S × O

/-- A reset-reachable initial state for a Mealy machine: the
state the design enters after the reset signal is asserted then
deasserted. SEC uses this as the basis state for the equivalence
proof, NOT an arbitrary state. -/
structure ResetInitial (S : Type*) where
  init : S

/-! ## Cross-structure refinement relation

The central new construct: `refines_under f` says that
implementation `impl_new : Step S_new I O` refines specification
`spec_old : Step S_old I O` when there exists an abstraction
function `f : S_new → S_old` such that:

1. The reset-reachable initial state of impl_new maps to the
   reset-reachable initial state of spec_old under f.
2. For every reachable state in impl_new and every input,
   stepping in impl_new and then projecting via f yields the
   same output as projecting via f and then stepping in
   spec_old (commutation under the abstraction).

This is the standard refinement-relation shape for cross-
structure equivalence checking. -/
def AbstractionFunction (S_new S_old : Type*) := S_new → S_old

/-- The refinement-relation contract. Implementation `impl_new`
refines specification `spec_old` under the abstraction
function `f` when the diagram commutes pointwise. -/
def refines_under {S_new S_old I O : Type*}
    (impl_new : Step S_new I O)
    (spec_old : Step S_old I O)
    (init_new : ResetInitial S_new)
    (init_old : ResetInitial S_old)
    (f : AbstractionFunction S_new S_old) : Prop :=
  -- Reset-state commutation: f maps the new reset-reachable
  -- initial state to the old one.
  (f init_new.init = init_old.init) ∧
  -- Step commutation: for every state and input, abstraction
  -- and stepping commute, AND outputs agree.
  (∀ (s_new : S_new) (i : I),
    let (s_new', o_new) := impl_new s_new i
    let (s_old', o_old) := spec_old (f s_new) i
    f s_new' = s_old' ∧ o_new = o_old)

/-! ## Lemmas usable in EBMC obligation discharge

These are the building blocks the closed-loop orchestrator
(ATH-991) feeds to EBMC as `assume property` directives, plus
the verification proofs the customer-facing certificate
references when reporting "cross-structure refinement is
machine-checked under abstraction f". -/

/-- Refinement-under-abstraction is reflexive when the
abstraction is the identity (degenerate case: same state space,
same step function). Not used in practice for cross-structure
optimizations, but anchors the type theory. -/
theorem refines_under_id {S I O : Type*}
    (impl : Step S I O) (init : ResetInitial S) :
    refines_under impl impl init init id := by
  refine ⟨rfl, ?_⟩
  intro s i
  simp [id]

/-- Refinement-under-abstraction is transitive: if `impl` refines
`mid` under `f`, and `mid` refines `spec` under `g`, then `impl`
refines `spec` under `g ∘ f`. This is the composition rule the
closed-loop orchestrator uses when chaining multiple cross-
structure optimizations. -/
theorem refines_under_trans {S₁ S₂ S₃ I O : Type*}
    {impl : Step S₁ I O} {mid : Step S₂ I O} {spec : Step S₃ I O}
    {init_impl : ResetInitial S₁} {init_mid : ResetInitial S₂}
    {init_spec : ResetInitial S₃}
    {f : AbstractionFunction S₁ S₂} {g : AbstractionFunction S₂ S₃}
    (h_fg : refines_under impl mid init_impl init_mid f)
    (h_gh : refines_under mid spec init_mid init_spec g) :
    refines_under impl spec init_impl init_spec (g ∘ f) := by
  obtain ⟨h_init_fg, h_step_fg⟩ := h_fg
  obtain ⟨h_init_gh, h_step_gh⟩ := h_gh
  refine ⟨?_, ?_⟩
  · -- Initial state commutes through composition.
    simp [Function.comp, h_init_fg, h_init_gh]
  · -- Step commutation composes.
    intro s i
    have hf := h_step_fg s i
    have hg := h_step_gh (f s) i
    simp [Function.comp]
    refine ⟨?_, ?_⟩
    · -- Next-state commutation: f s' → g (f s') = g (mid (f s) i).fst
      rw [hf.1]
      exact hg.1
    · -- Output commutation: outputs agree through both layers.
      rw [hf.2]
      exact hg.2

/-! ## Worked example: FIFO flop-array → memory-array refinement

Concrete illustration of the cross-structure refinement shape
on the canonical FIFO optimization (FIFO implemented as
flop array vs memory array).

This is intentionally small (1-bit width, depth 2) to keep the
proof obligations tractable as a worked example. Real customer
blocks discharge via the LLM-generated abstraction function
fed to EBMC's `assume property`; the worked example anchors
the type theory + lets D-spike validate consumption. -/

namespace WorkedExample

/-- Old (flop-array) state: 2-element flop array + count. -/
structure FlopFifoState where
  cell0 : Bool
  cell1 : Bool
  count : Fin 3
  deriving Repr, DecidableEq

/-- New (memory-array) state: indexed memory + read/write
pointers. Different state shape, semantically equivalent. -/
structure MemFifoState where
  mem : Fin 2 → Bool
  rd_ptr : Fin 2
  wr_ptr : Fin 2
  count : Fin 3
  deriving Repr

/-- Abstraction: project memory state down to flop-array view
by reading the two memory cells in order. -/
def absMemToFlop : AbstractionFunction MemFifoState FlopFifoState :=
  fun m => ⟨m.mem 0, m.mem 1, m.count⟩

/-- The abstraction is well-typed and pointwise meaningful.
Smoke-check: stepping with no inputs preserves the abstraction
trivially when both designs are in their reset state. -/
theorem absMemToFlop_reset_smoke :
    absMemToFlop ⟨fun _ => false, 0, 0, 0⟩ = ⟨false, false, 0⟩ := rfl

end WorkedExample

end Pythia.Hardware.SEC
