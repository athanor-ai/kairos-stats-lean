/-
Pythia.Hardware.ACL2Bridge — cross-engine composition layer for
ACL2 proof certificates in hardware refinement.

ACL2 produces unbounded refinement proofs for out-of-order
processors (FM9801 technique: flushing + inductive invariants).
EBMC produces bounded/unbounded proofs for tractable designs
(k-induction, BMC). Lean composes certificates from both engines
into a single unified proof.

Trust model: ACL2 and EBMC are trusted oracles. Their verdicts
enter Lean as axiomatically-assumed witnesses. The composition
logic (transitivity, NCS decomposition) is machine-checked in
Lean. This matches the CoqHammer architecture adapted for
multi-engine hardware verification.
-/
import Mathlib
import Pythia.Hardware.RefinementComposition

namespace Pythia.Hardware

/-- An external proof certificate from a trusted verification engine.
The certificate carries the engine name and a hash of the proof
transcript for auditability. -/
structure ProofCertificate where
  engine : String
  transcript_hash : String

/-- A witnessed refinement: a refinement claim backed by an external
proof certificate. The witness is trusted (the external engine
proved it); Lean records the composition. -/
structure WitnessedRefinement (n : ℕ)
    (implA implB : List ℤ → ArchState n) where
  claim : refines n implA implB
  certificate : ProofCertificate

/-- Compose two witnessed refinements from different engines.
For example: EBMC proves SI==PIPE, ACL2 proves PIPE==OOO,
Lean composes them into SI==OOO with both certificates recorded. -/
def composeWitnessed {n : ℕ}
    {implA implB implC : List ℤ → ArchState n}
    (wAB : WitnessedRefinement n implA implB)
    (wBC : WitnessedRefinement n implB implC) :
    WitnessedRefinement n implA implC :=
  { claim := refines_trans wAB.claim wBC.claim
    certificate :=
      { engine := wAB.certificate.engine ++ " + " ++ wBC.certificate.engine
        transcript_hash := wAB.certificate.transcript_hash ++ ":" ++
                          wBC.certificate.transcript_hash } }

/-- The three-way composition for Todd's CPU package:
EBMC certificate (SI==PIPE) + ACL2 certificate (PIPE==OOO)
= Lean-composed certificate (SI==OOO). -/
def threeWayComposition {n : ℕ}
    {si pipe ooo : List ℤ → ArchState n}
    (ebmc_cert : WitnessedRefinement n si pipe)
    (acl2_cert : WitnessedRefinement n pipe ooo) :
    WitnessedRefinement n si ooo :=
  composeWitnessed ebmc_cert acl2_cert

end Pythia.Hardware
