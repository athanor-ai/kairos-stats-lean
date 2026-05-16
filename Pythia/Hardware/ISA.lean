/-
Formal ISA property theorems for Trainium (ATH-1267, category 9).
Covers provably correct instruction encoding and privilege enforcement
for the Annapurna architecture. All theorems are stated with opaque
abstract types; proofs are deferred (sorry).
-/
import Mathlib

namespace Pythia.Hardware.ISA

opaque Opcode : Type
opaque Encoding : Type
opaque PrivilegeLevel : Type
opaque Instruction : Type
opaque ExceptionCode : Type
opaque MachineState : Type

opaque decode : Encoding → Option Instruction
opaque encode : Instruction → Encoding
opaque opcodeOf : Instruction → Opcode
opaque privilegeOf : MachineState → PrivilegeLevel
opaque exceptionPriority : ExceptionCode → ℕ
opaque userMode : PrivilegeLevel
opaque supervisorMode : PrivilegeLevel
opaque pcOf : MachineState → ℕ
opaque instrWidth : ℕ
opaque execute : Instruction → MachineState → MachineState
opaque isUserModeInstr : Instruction → Prop
opaque isValidEncoding : Encoding → Prop
opaque trapsToSupervisor : Instruction → MachineState → Prop

opaque instrWidth_pos : 0 < instrWidth

theorem encoding_injective :
    ∀ (i j : Instruction), encode i = encode j → i = j := by
  sorry

theorem opcode_decode_complete :
    ∀ (e : Encoding), isValidEncoding e → ∃! (i : Instruction), decode e = some i := by
  sorry

theorem immediate_sign_extension :
    ∀ (n m : ℕ) (v : ℤ), n < m →
    (-(2 : ℤ)^(n - 1) ≤ v ∧ v < 2^(n - 1)) →
    v % 2^n = v % 2^m := by
  sorry

theorem pc_increment_sound :
    ∀ (s : MachineState),
    instrWidth ∣ pcOf s →
    instrWidth ∣ (pcOf s + instrWidth) := by
  sorry

theorem exception_priority_total :
    ∀ (e₁ e₂ : ExceptionCode),
    e₁ ≠ e₂ →
    exceptionPriority e₁ ≠ exceptionPriority e₂ := by
  sorry

theorem privilege_escalation_impossible :
    ∀ (i : Instruction) (s : MachineState),
    isUserModeInstr i →
    privilegeOf s = userMode →
    ¬trapsToSupervisor i s →
    privilegeOf (execute i s) = userMode := by
  sorry

end Pythia.Hardware.ISA
