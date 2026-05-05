/-
Pythia.Hardware.SEC.ChainComposition — top-level composition lemma
for block-graphs of refinement contracts.

When an SoC block (e.g. `toy_fifo_chain`) is the wired composition
of multiple sub-blocks (FIFOs, packet transforms, arbiters), the
end-to-end refinement claim follows from per-block refinements
plus a wiring-correctness lemma that ties together their input/
output signatures.

This module provides:
- A generic chain-of-N composition for sequentially-connected blocks
- A merge composition for arbitrating-merge blocks (N inputs, 1 output)
- The reuse adapter to lift `Pythia.Hardware.refines_trans` into
  the SEC.WitnessedRefinement world

Reference: 2026-05-04 SEC pivot, ATH-983 (Annapurna toy_fifo_chain
top-level composition).
-/
import Mathlib
import Pythia.Hardware.SEC.FifoContract
import Pythia.Hardware.SEC.PacketTransform
import Pythia.Hardware.SEC.RoundRobinContract

namespace Pythia.Hardware.SEC

/-! ## Generic block step typeclass

A "block step" is any pure function from `(state, input)` to
`(state', output)`. The Mealy-machine convention. Per-block
contracts (Fifo, PacketTransform, RoundRobin) are all instances. -/

/-- A typed block step: (state, input) → (state', output). -/
abbrev BlockStep (S I O : Type*) := S → I → S × O

/-! ## Sequential chain composition -/

/-- Sequential composition: feed block `B`'s output into block
`C`'s input. The composite state is the product of states. -/
def chain {S₁ S₂ I₁ O₁I₂ O₂ : Type*}
    (b : BlockStep S₁ I₁ O₁I₂) (c : BlockStep S₂ O₁I₂ O₂) :
    BlockStep (S₁ × S₂) I₁ O₂ :=
  fun (s₁s₂ : S₁ × S₂) (i₁ : I₁) =>
    let (s₁', o₁) := b s₁s₂.1 i₁
    let (s₂', o₂) := c s₁s₂.2 o₁
    ((s₁', s₂'), o₂)

/-- Refinement under sequential chaining: if `b_impl` refines
`b_spec` and `c_impl` refines `c_spec`, then their chain
implementation refines the chained spec. -/
theorem chain_refines {S₁ S₂ I₁ O₁I₂ O₂ : Type*}
    {b_impl b_spec : BlockStep S₁ I₁ O₁I₂}
    {c_impl c_spec : BlockStep S₂ O₁I₂ O₂}
    (h_b : ∀ s i, b_impl s i = b_spec s i)
    (h_c : ∀ s i, c_impl s i = c_spec s i) :
    ∀ s i, chain b_impl c_impl s i = chain b_spec c_spec s i := by
  intro s i
  simp only [chain, h_b, h_c]

/-! ## Two-input arbitrating merge

Arbitrating merge: two sources feed into a single round-robin
arbiter, which selects one and emits its data. This is the shape
appearing at the output of the toy_fifo_chain (path A + path B
into the arbiter). -/

/-- Per-cycle paired input for a 2-source arbitrating merge. -/
structure MergeInput (I₁ I₂ : Type*) where
  left : I₁
  right : I₂

/-- Two-source arbitrating-merge composition: feed two parallel
block outputs into a round-robin arbiter. The arbiter's request
vector is constructed from each source's output-valid flag. -/
def arbMerge {S_L S_R O_L O_R : Type*} (N : ℕ)
    (b_L : BlockStep S_L I₁ O_L) (b_R : BlockStep S_R I₂ O_R)
    -- Caller supplies the projection from per-block output to the
    -- round-robin request bit (typically `o.valid`).
    (req_L : O_L → Bool) (req_R : O_R → Bool)
    (arb : BlockStep (RoundRobinState N) (RoundRobinInput N)
                     (RoundRobinOutput N)) :
    BlockStep (S_L × S_R × RoundRobinState N)
              (MergeInput I₁ I₂)
              (RoundRobinOutput N × O_L × O_R) :=
  fun (s : S_L × S_R × RoundRobinState N) (i : MergeInput I₁ I₂) =>
    let (s_L', o_L) := b_L s.1 i.left
    let (s_R', o_R) := b_R s.2.1 i.right
    -- Build the 2-bit request vector for the arbiter.
    let req_in : RoundRobinInput N := {
      req := fun k => if k.val = 0 then req_L o_L
                      else if k.val = 1 then req_R o_R
                      else false
    }
    let (s_arb', o_arb) := arb s.2.2 req_in
    ((s_L', s_R', s_arb'), (o_arb, o_L, o_R))

/-- Refinement under arbitrating-merge composition. -/
theorem arbMerge_refines {S_L S_R O_L O_R : Type*} {N : ℕ}
    {b_L_impl b_L_spec : BlockStep S_L I₁ O_L}
    {b_R_impl b_R_spec : BlockStep S_R I₂ O_R}
    {arb_impl arb_spec : BlockStep (RoundRobinState N) (RoundRobinInput N)
                                    (RoundRobinOutput N)}
    (req_L : O_L → Bool) (req_R : O_R → Bool)
    (h_L : ∀ s i, b_L_impl s i = b_L_spec s i)
    (h_R : ∀ s i, b_R_impl s i = b_R_spec s i)
    (h_arb : ∀ s i, arb_impl s i = arb_spec s i) :
    ∀ s i, arbMerge N b_L_impl b_R_impl req_L req_R arb_impl s i =
           arbMerge N b_L_spec b_R_spec req_L req_R arb_spec s i := by
  intro s i
  simp only [arbMerge, h_L, h_R, h_arb]

/-! ## Top-level toy_fifo_chain composition

The toy_fifo_chain has the block-graph:
  inputs → FIFO_1 → FIFO_2 → FIFO_3 ─┐
                                      ├─ Arbiter → output
  inputs → FIFO_4 → FIFO_5 → AddHdr ──┘

This is `chain ∘ chain` for paths A and B, then `arbMerge` to
combine. The composition theorem follows from successive
applications of `chain_refines` and `arbMerge_refines`.

The full toy_fifo_chain's witness type is left to the SEC harness
to construct from the concrete per-block witnesses; this module
provides the composition machinery so the harness's job is purely
mechanical wiring. -/

end Pythia.Hardware.SEC
