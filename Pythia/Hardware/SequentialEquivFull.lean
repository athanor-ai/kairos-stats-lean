import Mathlib

-- Full sequential equivalence (not just BMC-bounded).
-- Prove that if two FSMs have bisimilar state spaces,
-- they produce identical output sequences on all inputs.

variable {State1 State2 Input Output : Type*}

structure FSM (State Input Output : Type*) where
  init : State
  next : State → Input → State
  out  : State → Output

-- Bisimulation relation
def isBisimulation (R : State1 → State2 → Prop)
    (m1 : FSM State1 Input Output) (m2 : FSM State2 Input Output) : Prop :=
  R m1.init m2.init ∧
  ∀ s1 s2, R s1 s2 → m1.out s1 = m2.out s2 ∧
    ∀ i : Input, R (m1.next s1 i) (m2.next s2 i)

/-
If a bisimulation exists, the FSMs produce identical output sequences
-/
theorem bisimulation_implies_trace_equiv
    (m1 : FSM State1 Input Output) (m2 : FSM State2 Input Output)
    (R : State1 → State2 → Prop)
    (h : isBisimulation R m1 m2) :
    ∀ (n : ℕ) (inputs : Fin n → Input),
      m1.out (List.ofFn inputs |>.foldl m1.next m1.init) =
      m2.out (List.ofFn inputs |>.foldl m2.next m2.init) := by
  -- By definition of bisimulation, we know that if `R s1 s2`, then `m1.out s1 = m2.out s2`.
  intros n inputs
  have h_ind : ∀ s1 s2, R s1 s2 → ∀ is, R (List.foldl m1.next s1 is) (List.foldl m2.next s2 is) := by
    intro s1 s2 hR is;
    induction' is using List.reverseRecOn with is ih;
    · exact hR;
    · simpa using h.2 _ _ ‹_› |>.2 ih;
  exact h.2 _ _ ( h_ind _ _ h.1 _ ) |>.1

/-
Bisimulation is symmetric
-/
theorem bisimulation_symmetric
    (m1 : FSM State1 Input Output) (m2 : FSM State2 Input Output)
    (R : State1 → State2 → Prop)
    (h : isBisimulation R m1 m2) :
    isBisimulation (fun s2 s1 => R s1 s2) m2 m1 := by
  grind +locals

/-
Bisimulation composes transitively
-/
theorem bisimulation_transitive
    {State3 : Type*}
    (m1 : FSM State1 Input Output) (m2 : FSM State2 Input Output)
    (m3 : FSM State3 Input Output)
    (R12 : State1 → State2 → Prop) (R23 : State2 → State3 → Prop)
    (h12 : isBisimulation R12 m1 m2) (h23 : isBisimulation R23 m2 m3) :
    isBisimulation (fun s1 s3 => ∃ s2, R12 s1 s2 ∧ R23 s2 s3) m1 m3 := by
  unfold isBisimulation at *;
  grind