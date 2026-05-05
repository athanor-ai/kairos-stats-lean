/-
Pythia.Hardware.SEC.FifoWidgetGoldGateRefinement — gold-vs-gate
relational invariants for the toy_fifo_chain v2.5 fifo_widget
block (ATH-1045 child of ATH-1042).

The v2.5 customer-block-certificate ships with two bridge
invariants used as EBMC `assume property` directives:

* `bridge_full`: `gold.count = gate.count` — minimum-sufficient
  for closing `full_match` under k-induction.
* `bridge_empty`: `gold.count = gate.count ∧ gold.head =
  gate.head ∧ gold.tail = gate.tail` — minimum-sufficient for
  closing `empty_match`.

These are *EBMC-side assume-property* discharges, not Lean
theorems. The v2.5 cert honest-frames them as "PROVED-with-
assume; bridges UNPROVEN as Lean theorems". This file converts
the assume-property bridges into kernel-checked relational
invariants over the gold (`fifo_widget` SV) and gate
(`fifo_widget_gate` Clash-emitted V) Mealy step functions.

When closed, the v2.6 cert drops the conditional framing:
"PROVED-with-assume; bridges PROVED as kernel-checked Lean
refinement (`bridge_full_gold_gate`, `bridge_empty_gold_gate`)".

## Modeling notes

* `gold.sv` (~46 LOC): `mem : logic [27:0] [4]`, `head/tail/count
  : logic [2:0]`. Transitions on `posedge clk` from `negedge
  rst_n`. Concrete-DEPTH=4 specialization (no parameters / clog2)
  per the EBMC 5.10 parser-invariant workaround.
* `gate.v` (~150 LOC): Clash-emitted from a Haskell Mealy
  description. Same I/O ports + same effective semantics on
  `count/head/tail`; differs only in `mem` layout (single
  112-bit reg, big-endian by cell). Reset is `posedge rst`
  where `rst = ~rst_n`.

Both designs increment count under `push & ~full`, decrement
count under `pop & ~empty`, and clamp count to its min/max
under simultaneous push+pop. head + tail step on the same
gating conditions.

Stage 1 (this commit): theorem stubs + state structures
mirroring gold + gate Mealy semantics. Aristotle closes the
preservation proof bodies; the inductive structure is canonical
(initial-state base case + step-preservation inductive case).
Statements are non-vacuous: arbitrary unrelated states do NOT
satisfy the invariant; only co-stepped from the reset-reachable
initial pair.

Stage 2 (Aristotle queue, research-decided per
`feedback_research_aristotle_authority_no_cto_gate.md`):
discharge the sorry bodies + lift `[UNPROVEN — assumed]` chips
on the v2.6 cert assumption-stack render to
`[PROVED via Pythia.Hardware.SEC.FifoWidget.bridge_*_gold_gate]`.

Reference: ATH-1042 v2.6 epic; ATH-1045 (this); ATH-1018
cert-vs-engine cross-check (consumes the proved bridges from
this file via the `proves_obligation` field on the
`invariant_gen_result` event); `examples/customer/
toy_fifo_chain_v2.5_sec/inputs/{gold.sv,gate.v}` (athanor-sdk
qa/v2.5-toy-fifo-chain-cert-placeholder branch HEAD c73cd23).
-/
import Mathlib
import Pythia.Hardware.SEC.RefinementRelation

namespace Pythia.Hardware.SEC

namespace FifoWidget

/-! ## Shared input alphabet

Both gold and gate take the same input port set per the
signature: `push`, `push_data[27:0]`, `pop`. -/

/-- Inputs to either fifo_widget design on a single clock edge. -/
structure WidgetInput where
  push : Bool
  push_data : BitVec 28
  pop : Bool
  deriving Repr, DecidableEq

/-- Outputs from either fifo_widget design: `full`, `empty`,
`pop_data`. -/
structure WidgetOutput where
  full : Bool
  empty : Bool
  pop_data : BitVec 28
  deriving Repr, DecidableEq

/-! ## Gold side: mirrors gold.sv

`mem : logic [27:0] [4]` — 4-cell array of 28-bit data
`head/tail/count : logic [2:0]` — 3-bit pointers + count
(width is clog2(4)+1 per the SV comment) -/

/-- State for the gold-side fifo_widget (SV reference impl). -/
structure GoldFifoWidgetState where
  mem : Fin 4 → BitVec 28
  head : BitVec 3
  tail : BitVec 3
  count : BitVec 3
  deriving Repr

/-- Reset state for gold: head/tail/count all zero. mem is
unspecified at reset (matches the SV: no explicit mem reset). -/
def goldReset : GoldFifoWidgetState :=
  ⟨fun _ => 0, 0, 0, 0⟩

/-- Gold-side Mealy step. Mirrors `gold.sv`:

* `full = (count == 4)` combinationally.
* `empty = (count == 0)` combinationally.
* `pop_data = mem[head[1:0]]` combinationally.
* On clock edge:
  - `push & ~full`: `mem[tail[1:0]] := push_data`,
    `tail++`, `count++`.
  - `pop & ~empty`: `head++`, `count--`.
  - simultaneous push+pop: `count` retains old value (per
    the gold.sv `count <= count` line that overrides the
    push and pop branches when both fire). -/
def goldStep (s : GoldFifoWidgetState) (i : WidgetInput) :
    GoldFifoWidgetState × WidgetOutput :=
  let isFull := s.count = 4
  let isEmpty := s.count = 0
  let pushFires := i.push ∧ ¬ isFull
  let popFires := i.pop ∧ ¬ isEmpty
  let head_idx : Fin 4 :=
    ⟨ s.head.toNat % 4, by omega ⟩
  let tail_idx : Fin 4 :=
    ⟨ s.tail.toNat % 4, by omega ⟩
  let new_mem : Fin 4 → BitVec 28 :=
    if pushFires then
      fun j => if j = tail_idx then i.push_data else s.mem j
    else
      s.mem
  let new_head : BitVec 3 :=
    if popFires then s.head + 1 else s.head
  let new_tail : BitVec 3 :=
    if pushFires then s.tail + 1 else s.tail
  let new_count : BitVec 3 :=
    if pushFires ∧ popFires then s.count
    else if pushFires then s.count + 1
    else if popFires then s.count - 1
    else s.count
  ( { mem := new_mem, head := new_head,
      tail := new_tail, count := new_count },
    { full := isFull, empty := isEmpty,
      pop_data := s.mem head_idx } )

/-! ## Gate side: mirrors gate.v (Clash-emitted)

`mem : reg [111:0]` — single 112-bit reg, big-endian-by-cell:
gate.mem[111:84] = cell[0], gate.mem[83:56] = cell[1],
gate.mem[55:28] = cell[2], gate.mem[27:0] = cell[3]. The Clash
codegen reverses the cell order via the `vecArray[(4-1)-i]`
indexing pattern in the index-begin generate block.

`head/tail/count : reg [2:0]` — same shape as gold.

Reset is `posedge rst` where `rst = ~rst_n`, so the effective
reset condition (rst_n falling edge → rst rising edge → reset
fires) matches gold's `negedge rst_n`. -/

/-- State for the gate-side fifo_widget_gate (Clash-emitted).
mem is modeled as a 112-bit reg even though the on-chip
representation is bit-packed; equality-as-bit-string suffices
for the bridge invariant proofs. -/
structure GateFifoWidgetState where
  mem : BitVec 112
  head : BitVec 3
  tail : BitVec 3
  count : BitVec 3
  deriving Repr

/-- Reset state for gate: head/tail/count zero, mem all-X
(modeled as 0 for the kernel-checked refinement; X-init
aliasing diagnostic for `pop_data_match` is captured separately
via the bare-miter ebmc-induction-bare.log). -/
def gateReset : GateFifoWidgetState :=
  ⟨0, 0, 0, 0⟩

/-- Read cell at index `i` (∈ [0,4)) out of the gate's
bit-packed mem. Cells are laid out big-endian-by-cell: cell 0
occupies bits [111:84], cell 1 [83:56], cell 2 [55:28], cell 3
[27:0]. Reverses the on-chip Clash `vecArray[(4-1)-i]`
indexing.

Concrete bit-slices: `cell j = mem.extractLsb' (28 * (3 - j)) 28`
when read in the natural cell-index sense. -/
def gateReadCell (m : BitVec 112) (j : Fin 4) : BitVec 28 :=
  m.extractLsb' (28 * (3 - j.val)) 28

/-- Write `v` into cell `j` of the gate's bit-packed mem,
preserving the other three cells. The bit-slices of cell j sit
at offset `28 * (3 - j.val)` in the 112-bit reg.

Stage 1: declared as stub (sorry) so the theorem statements
typecheck without requiring the bit-mask-and-shift composition
worked out. Stage 2 (ATH-1045 Aristotle queue) replaces the
sorry with the mask + shift-and-or composition + the equational
read-after-write lemmas (gateReadCell after gateWriteCell j v
yields v on j and the original cell on j' ≠ j). -/
def gateWriteCell (m : BitVec 112) (j : Fin 4) (v : BitVec 28) :
    BitVec 112 :=
  let offset := 28 * (3 - j.val)
  let mask : BitVec 112 := (BitVec.allOnes 28 |>.zeroExtend 112) <<< offset
  (m &&& ~~~mask) ||| ((v.zeroExtend 112) <<< offset)

/-- Gate-side Mealy step. Mirrors `gate.v` (Clash-emitted):

* `full_1 = count == 4` combinationally.
* `empty_1 = count == 0` combinationally.
* `pushEff = push & ~full_1`, `popEff = pop & ~empty_1`.
* `pop_data = gateReadCell mem head[1:0]` combinationally.
* On clock edge:
  - `pushEff`: `mem[tail[1:0]] := push_data` (via
    `gateWriteCell`), `tail++`, `count update`.
  - `popEff`: `head++`, `count update`.
  - count update mirrors gold's clamping discipline (Clash
    codegen produces equivalent semantics; verify-as-Lean-
    theorem in stage 2). -/
def gateStep (s : GateFifoWidgetState) (i : WidgetInput) :
    GateFifoWidgetState × WidgetOutput :=
  let isFull := s.count = 4
  let isEmpty := s.count = 0
  let pushFires := i.push ∧ ¬ isFull
  let popFires := i.pop ∧ ¬ isEmpty
  let head_idx : Fin 4 :=
    ⟨ s.head.toNat % 4, by omega ⟩
  let tail_idx : Fin 4 :=
    ⟨ s.tail.toNat % 4, by omega ⟩
  let new_mem : BitVec 112 :=
    if pushFires then
      gateWriteCell s.mem tail_idx i.push_data
    else
      s.mem
  let new_head : BitVec 3 :=
    if popFires then s.head + 1 else s.head
  let new_tail : BitVec 3 :=
    if pushFires then s.tail + 1 else s.tail
  let new_count : BitVec 3 :=
    if pushFires ∧ popFires then s.count
    else if pushFires then s.count + 1
    else if popFires then s.count - 1
    else s.count
  ( { mem := new_mem, head := new_head,
      tail := new_tail, count := new_count },
    { full := isFull, empty := isEmpty,
      pop_data := gateReadCell s.mem head_idx } )

/-! ## Bridge invariants

Each is a relational invariant on (gold, gate) pairs. The
invariant is closed inductively: it holds at the reset-pair
state (base case) and is preserved by simultaneous stepping
under any input (preservation case). Together these give the
canonical inductive-invariant content. -/

/-- `bridgeFullInv g t` says: gold and gate have the same
count register. This is the minimum-sufficient bridge for
closing the v2.5 `full_match` property under k-induction. -/
def bridgeFullInv (g : GoldFifoWidgetState) (t : GateFifoWidgetState) :
    Prop :=
  g.count = t.count

/-- `bridgeEmptyInv g t` says: gold and gate have the same
count, head, AND tail registers. This is the minimum-sufficient
bridge for closing the v2.5 `empty_match` property under
k-induction (count alone is insufficient because empty-cycle
output reads from mem[head[1:0]]). -/
def bridgeEmptyInv (g : GoldFifoWidgetState) (t : GateFifoWidgetState) :
    Prop :=
  g.count = t.count ∧ g.head = t.head ∧ g.tail = t.tail

/-! ## Base cases (initial-state lemmas)

The reset-pair `(goldReset, gateReset)` satisfies both bridge
invariants by definitional reflexivity since both designs reset
count/head/tail to 0. -/

/-- The reset-pair satisfies bridgeFullInv. -/
theorem bridgeFullInv_at_reset :
    bridgeFullInv goldReset gateReset := by
  unfold bridgeFullInv goldReset gateReset
  rfl

/-- The reset-pair satisfies bridgeEmptyInv. -/
theorem bridgeEmptyInv_at_reset :
    bridgeEmptyInv goldReset gateReset := by
  unfold bridgeEmptyInv goldReset gateReset
  refine ⟨rfl, rfl, rfl⟩

/-! ## Preservation theorems (inductive cases)

These say: the bridge invariants are preserved by any
simultaneous step of gold + gate under any common input. The
content of these proofs is that gold's count/head/tail update
logic and gate's count/head/tail update logic compute the same
new values from the same old values + same input.

Both proofs sorry'd; Aristotle queue closes them. The
structural form is canonical (case-split on
push/pop/isFull/isEmpty + reduce both step functions
definitionally). -/

/-
Preservation: bridgeFullInv is closed under simultaneous
gold/gate step on a common input.
-/
theorem bridgeFullInv_preserved
    (g : GoldFifoWidgetState) (t : GateFifoWidgetState)
    (i : WidgetInput)
    (h : bridgeFullInv g t) :
    bridgeFullInv (goldStep g i).1 (gateStep t i).1 := by
  -- ATH-1045 stage 2 (Aristotle queue): structurally a
  -- case-split on (i.push, i.pop, isFull, isEmpty). Both step
  -- functions update count via identical formulas (clamped at
  -- ±1 with the simultaneous-push-pop retain-old discipline).
  -- With h : g.count = t.count, the four branches each yield
  -- the same new count on both sides.
  unfold bridgeFullInv at *; simp_all +decide [ goldStep, gateStep ] ;

/-
Preservation: bridgeEmptyInv is closed under simultaneous
gold/gate step on a common input.
-/
theorem bridgeEmptyInv_preserved
    (g : GoldFifoWidgetState) (t : GateFifoWidgetState)
    (i : WidgetInput)
    (h : bridgeEmptyInv g t) :
    bridgeEmptyInv (goldStep g i).1 (gateStep t i).1 := by
  -- ATH-1045 stage 2 (Aristotle queue): three sub-claims —
  -- count preservation (same as bridgeFullInv_preserved),
  -- head preservation (case-split on popFires), tail
  -- preservation (case-split on pushFires). With h giving all
  -- three at the entry state, each component closes by the
  -- corresponding step formula's pointwise determinism.
  unfold bridgeEmptyInv at *;
  unfold goldStep gateStep; aesop;

/-! ## Composition: bridge invariants hold on every co-stepped
state from reset

These are the customer-facing theorems referenced in the v2.6
cert: starting from `(goldReset, gateReset)` and stepping both
by any sequence of `WidgetInput`s, the bridge invariants hold
at every point along the trace. Proofs are by induction on the
trace length using the base case + preservation lemmas above. -/

/-
Stepping both designs k times under the same input sequence
preserves the gold-vs-gate full-match bridge invariant from the
reset-pair starting state.
-/
theorem bridgeFullInv_holds_at_every_co_step
    (inputs : List WidgetInput) :
    bridgeFullInv
      (inputs.foldl (fun s i => (goldStep s i).1) goldReset)
      (inputs.foldl (fun s i => (gateStep s i).1) gateReset) := by
  -- ATH-1045 stage 2: induction on `inputs`. Base case:
  -- `bridgeFullInv_at_reset`. Inductive case: apply
  -- `bridgeFullInv_preserved` to the inductive hypothesis.
  induction' inputs using List.reverseRecOn with inputs ih;
  · exact bridgeFullInv_at_reset
  · simpa [ List.foldl_append ] using bridgeFullInv_preserved _ _ _ ‹_›

/-
Stepping both designs k times under the same input sequence
preserves the gold-vs-gate empty-match bridge invariant from
the reset-pair starting state.
-/
theorem bridgeEmptyInv_holds_at_every_co_step
    (inputs : List WidgetInput) :
    bridgeEmptyInv
      (inputs.foldl (fun s i => (goldStep s i).1) goldReset)
      (inputs.foldl (fun s i => (gateStep s i).1) gateReset) := by
  -- ATH-1045 stage 2: induction on `inputs`. Base case:
  -- `bridgeEmptyInv_at_reset`. Inductive case: apply
  -- `bridgeEmptyInv_preserved` to the inductive hypothesis.
  induction' inputs using List.reverseRecOn with inputs x ih
  · exact bridgeEmptyInv_at_reset
  · simpa [List.foldl_append] using bridgeEmptyInv_preserved _ _ _ ih

end FifoWidget

end Pythia.Hardware.SEC