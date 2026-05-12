/-
Pythia.Hardware.SEC.PacketTransform — pure-function refinement
contract for combinational packet-transform blocks (e.g.
`add_header`-class designs that map an input packet to an output
packet without retained state).

Customer use: blocks where the SystemVerilog gold's body is a single
`always_comb` doing pure combinational logic refine this contract
when their function-of-input matches the spec function. EBMC
discharges the per-cycle equality check; Lean records the witnessed
refinement.

Reference: 2026-05-04 SEC pivot, ATH-XXX.
-/
import Mathlib

namespace Pythia.Hardware.SEC

/-! ## Abstract packet types -/

/-- An abstract packet of payload width `w` plus a header of
width `h`. The bit-vector representation matches a single
contiguous `BitVec (h + w)` in the SystemVerilog port. -/
structure Packet (h w : ℕ) where
  header : BitVec h
  payload : BitVec w
  deriving Repr

/-! ## The pure-function refinement -/

/-- A combinational packet transform is a pure function from input
packet to output packet. No state, no clock dependence. The Mealy
machine collapses to a stateless map. -/
abbrev PacketTransform (h₁ w₁ h₂ w₂ : ℕ) :=
  Packet h₁ w₁ → Packet h₂ w₂

/-- Refinement for packet transforms: implementation `impl` refines
spec `spec` if they compute the same function pointwise. -/
def implementsTransform {h₁ w₁ h₂ w₂ : ℕ}
    (impl spec : PacketTransform h₁ w₁ h₂ w₂) : Prop :=
  ∀ p : Packet h₁ w₁, impl p = spec p

/-! ## Worked example: `add_header` shape -/

/-- Constant-header-prepend transform: output's header is a fixed
constant, output's payload is the entire input packet (header ++
payload) bit-concatenated. This matches the toy demo's
`add_header` block shape. -/
def addHeader {h_in w_in h_out : ℕ}
    (const_header : BitVec h_out) :
    PacketTransform h_in w_in h_out (h_in + w_in) :=
  fun p => {
    header := const_header
    payload := p.header ++ p.payload
  }

/-! ## Lemmas usable for EBMC obligation discharge -/

/-- The header of `addHeader` output is the supplied constant,
independent of input. -/
theorem addHeader_header_const {h_in w_in h_out : ℕ}
    (c : BitVec h_out) (p : Packet h_in w_in) :
    (addHeader c p).header = c := rfl

/-- The payload of `addHeader` output preserves the full input
packet (header concatenated with payload). This is the
`transform_field_preservation` obligation in the toy demo's
verdict mix. -/
theorem addHeader_payload_preserves_input {h_in w_in h_out : ℕ}
    (c : BitVec h_out) (p : Packet h_in w_in) :
    (addHeader c p).payload = p.header ++ p.payload := rfl

/-! ## Composition with EBMC certificate -/

/-- A combinational EBMC witness: the transform's pure-function
equality is bounded-model-checked at each input bit-pattern (BMC
exhausts the input space when its small enough; k-induction
discharges with a one-step argument since there's no state). -/
structure PacketTransformEBMCWitness {h₁ w₁ h₂ w₂ : ℕ}
    (impl spec : PacketTransform h₁ w₁ h₂ w₂) where
  refines : implementsTransform impl spec
  /-- Engine: "ebmc-bmc" or "ebmc-k_induction". -/
  engine : String
  /-- Hash of the EBMC transcript for auditability. -/
  transcript_hash : String

end Pythia.Hardware.SEC
