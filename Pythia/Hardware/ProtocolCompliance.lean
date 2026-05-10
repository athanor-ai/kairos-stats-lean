import Mathlib

-- Protocol compliance checker: verify that a trace of events
-- satisfies a protocol specification (sequence of allowed transitions).
-- General framework for any protocol (AXI, AHB, Wishbone, etc.)

variable {Event : Type*}

-- A protocol is a set of allowed transitions
structure Protocol (Event : Type*) where
  allowed : Event → Event → Prop
  initial : Event → Prop

-- A trace is compliant if every consecutive pair is allowed
def isCompliant (p : Protocol Event) (trace : List Event) : Prop :=
  (∀ e ∈ trace.head?, p.initial e) ∧
  ∀ i (hi : i + 1 < trace.length),
    p.allowed (trace.get ⟨i, by omega⟩) (trace.get ⟨i + 1, hi⟩)

/-
Empty trace is compliant
-/
theorem empty_compliant (p : Protocol Event) :
    isCompliant p [] := by
  constructor <;> tauto

/-
Single-event trace is compliant if initial
-/
theorem single_compliant (p : Protocol Event) (e : Event) (h : p.initial e) :
    isCompliant p [e] := by
  constructor <;> simp +decide [ h ]

/-
Extending a compliant trace with an allowed event stays compliant
-/
theorem extend_compliant (p : Protocol Event) (trace : List Event) (e : Event)
    (h_comp : isCompliant p trace) (h_nonempty : trace ≠ [])
    (h_allowed : p.allowed (trace.getLast h_nonempty) e) :
    isCompliant p (trace ++ [e]) := by
  constructor;
  · cases trace <;> simp_all +decide;
    · contradiction;
    · exact h_comp.1 _ ( by simp +decide );
  · intro i hi; by_cases hi' : i < trace.length <;> simp_all +decide [ List.getElem_append ] ;
    · split_ifs with h <;> simp_all +decide [ isCompliant ];
      grind;
    · grind