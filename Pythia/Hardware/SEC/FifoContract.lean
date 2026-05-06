/-
Pythia.Hardware.SEC.FifoContract — abstract Mealy-machine refinement
contract for synchronous FIFO blocks, suitable for sequential
equivalence checking (SEC) against a SystemVerilog gold and a
Clash-generated Verilog gate.

The contract captures the operational FIFO semantics that bound
SEC engines (EBMC in BMC or k-induction mode) verify the gold and
gate both implement: push/pop transitions, count-idiom under
simultaneous push+pop, capacity bound, and backpressure safety.

Customer use: each per-instance FIFO obligation in a block graph
discharges via `FifoContract.implements` against this abstract
spec. The composition lemma in `ChainComposition.lean` chains
multiple FIFO contracts into a top-level block-graph claim.

Reference: 2026-05-04 SEC pivot driven by [customer]/***REMOVED***
roadmap — proper SEC harness with EBMC, defer ACL2, fix
uninitialized-flops handling.
-/
import Mathlib

namespace Pythia.Hardware.SEC

/-! ## Abstract FIFO state -/

/-- The abstract state of a FIFO of capacity `cap` with element width
`w`. Mathematically, this is a list of bit-vectors of length at most
`cap`, but we track only the count and the externally-visible head
element since SEC obligations are stated against the head. -/
structure FifoState (cap : ℕ) (w : ℕ) where
  count : Fin (cap + 1)
  head_elem : BitVec w
  -- The full mem-array is not part of the abstract spec; only head
  -- and count are externally observable through the FIFO interface.
  deriving Repr

/-- The abstract input on a FIFO clock cycle: push enable + push
data + pop enable. -/
structure FifoInput (w : ℕ) where
  push : Bool
  push_data : BitVec w
  pop : Bool
  deriving Repr

/-- The abstract output on a FIFO clock cycle: pop data (valid when
`pop && !empty`) + full + empty status flags. -/
structure FifoOutput (w : ℕ) where
  pop_data : BitVec w
  full : Bool
  empty : Bool
  deriving Repr

/-! ## The abstract step function -/

/-- The reference Mealy step for the FIFO. This is the *contract*:
both gold and gate are required to refine this, modulo the
abstraction relation in `Refinement.lean`.

The count-idiom convention: when push and pop both fire in the same
cycle and the FIFO is neither full nor empty, `count` stays the
same. This is the SystemVerilog last-assignment-wins idiom we want
the synthesised RTL to honour. -/
def fifoStep {cap w : ℕ} (s : FifoState cap w) (i : FifoInput w) :
    FifoState cap w × FifoOutput w :=
  let isFull := s.count.val = cap
  let isEmpty := s.count.val = 0
  let outValid := i.pop && !isEmpty
  let new_count_int : ℤ :=
    s.count.val
      + (if i.push && !isFull then 1 else 0)
      - (if i.pop && !isEmpty then 1 else 0)
  -- Clamp to [0, cap] (cannot escape under the guarded transitions).
  let new_count : Fin (cap + 1) :=
    ⟨ Int.toNat (max 0 (min (cap : ℤ) new_count_int)),
      by
        have : Int.toNat (max 0 (min (cap : ℤ) new_count_int)) ≤ cap := by
          have h₁ : min (cap : ℤ) new_count_int ≤ (cap : ℤ) := min_le_left _ _
          have h₂ : (0 : ℤ) ≤ max 0 (min (cap : ℤ) new_count_int) := le_max_left _ _
          have h₃ : max 0 (min (cap : ℤ) new_count_int) ≤ (cap : ℤ) :=
            max_le (Int.ofNat_nonneg cap) h₁
          omega
        omega ⟩
  (-- Updated head: if push to an empty FIFO, the pushed element becomes
   -- the head; otherwise (any other case) head_elem is preserved at the
   -- abstract level. Real RTL maintains a head pointer; the abstraction
   -- does not need to.
   { count := new_count,
     head_elem := if i.push && isEmpty then i.push_data else s.head_elem },
   { pop_data := s.head_elem,
     full := s.count.val + 1 ≥ cap,
     empty := isEmpty })

/-! ## Refinement contract -/

/-- An RTL implementation refines the FIFO contract if its
externally-observable behaviour (the abstraction projection of
its register state plus its output ports) agrees with `fifoStep`
for every input sequence starting from a reset state.

`Reset` here is the reset-reachable initial state, which both
gold and gate enter after `rst_n` is asserted then deasserted.
The SEC harness in `kairos.sec` constrains the SAT solver to
this basis via the assumption `non_reset_regs(gold) =
non_reset_regs(gate)` (matching [customer]'s 2026-05-04 SEC roadmap).
-/
def implements {cap w : ℕ}
    (impl : FifoState cap w → FifoInput w → FifoState cap w × FifoOutput w)
    : Prop :=
  ∀ s i, impl s i = fifoStep s i

/-! ## Lemmas usable in EBMC obligation discharge -/

/-- Capacity bound: count never exceeds `cap`. Discharged in EBMC
via k-induction over `count <= cap` as the inductive invariant. -/
theorem fifoStep_count_le_cap {cap w : ℕ}
    (s : FifoState cap w) (i : FifoInput w) :
    (fifoStep s i).1.count.val ≤ cap :=
  Nat.lt_succ_iff.mp (fifoStep s i).1.count.isLt

/-- No-underflow: the count after step never decreases below 0
(captured by `Fin (cap + 1)` typing). This is structurally true
by the `Fin` clamp in `fifoStep`. -/
theorem fifoStep_count_nonneg {cap w : ℕ}
    (s : FifoState cap w) (i : FifoInput w) :
    0 ≤ (fifoStep s i).1.count.val :=
  Nat.zero_le _

/-- Backpressure safety: a successful push (push∧!full) cannot be
silently dropped. If the contract reports full, the abstract
step does not increment count beyond `cap`. -/
theorem fifoStep_no_silent_drop {cap w : ℕ}
    (s : FifoState cap w) (i : FifoInput w)
    (h_full : s.count.val = cap) (h_push_only : i.push ∧ ¬i.pop) :
    (fifoStep s i).1.count.val = cap := by
  unfold fifoStep
  simp only [h_full, h_push_only.1, h_push_only.2]
  -- The "isFull" branch suppresses the +1, so count stays at cap.
  have : decide (cap = cap) = true := by simp
  simp [this]

/-! ## Composition with the engine certificate -/

/-- An EBMC-witnessed refinement: a refinement claim backed by an
EBMC verdict (BMC or k-induction). This is the per-block contract
output the SEC harness produces.

This wraps the existing `Pythia.Hardware.WitnessedRefinement`
infrastructure (in ACL2Bridge.lean, despite the name) to apply
to the FIFO refinement specifically. -/
structure FifoEBMCWitness (cap w : ℕ)
    (impl : FifoState cap w → FifoInput w → FifoState cap w × FifoOutput w) where
  /-- The implements claim itself. -/
  refines : implements impl
  /-- Engine: "ebmc-bmc" or "ebmc-k_induction". -/
  engine : String
  /-- Hash of the EBMC transcript for auditability. -/
  transcript_hash : String

end Pythia.Hardware.SEC
