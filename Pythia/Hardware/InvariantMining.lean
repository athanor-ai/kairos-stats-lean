import Mathlib

-- Invariant mining from simulation traces.
-- If a property holds on all observed traces, it is a candidate invariant.
-- Soundness: a mined invariant that passes k-induction IS an invariant.

variable {State : Type*}

-- A trace is a finite sequence of states
def traceProperty (P : State → Prop) (trace : List State) : Prop :=
  ∀ s ∈ trace, P s

-- If P holds on all traces in a trace set, P is a candidate invariant
def candidateInvariant (P : State → Prop) (traces : List (List State)) : Prop :=
  ∀ trace ∈ traces, traceProperty P trace

-- Original (incorrect) definition of k-inductive invariant.
-- The base case `∀ s, init s → P s` only covers step 0, but k-induction
-- for k ≥ 1 requires P to hold on the first k+1 reachable states.
--
-- Counterexample for k=1: State = Fin 3, init s ↔ s=0, next = {(0,1),(1,2)},
-- P s ↔ s≠1. Then h.1 and h.2 hold (h.2 vacuously), but trace ![0,1] violates P
-- at step 1.
--
-- def kInductiveInvariant_ORIGINAL (P : State → Prop) (init : State → Prop)
--     (next : State → State → Prop) (k : ℕ) : Prop :=
--   (∀ s, init s → P s) ∧
--   (∀ (trace : Fin (k + 2) → State),
--     (∀ i : Fin (k + 1), next (trace i.castSucc) (trace i.succ)) →
--     (∀ i : Fin (k + 1), P (trace i.castSucc)) →
--     P (trace ⟨k + 1, by omega⟩))

/-- Corrected k-induction: the base case requires P to hold at every step ≤ k
    along any trace from an initial state. This matches the standard definition
    used in model checking (Sheeran–Singh–Stålmarck 2000). -/
def kInductiveInvariant (P : State → Prop) (init : State → Prop)
    (next : State → State → Prop) (k : ℕ) : Prop :=
  (∀ (n : ℕ) (_ : n ≤ k) (trace : Fin (n + 1) → State),
    init (trace 0) →
    (∀ i : Fin n, next (trace i.castSucc) (trace i.succ)) →
    P (trace ⟨n, by omega⟩)) ∧
  (∀ (trace : Fin (k + 2) → State),
    (∀ i : Fin (k + 1), next (trace i.castSucc) (trace i.succ)) →
    (∀ i : Fin (k + 1), P (trace i.castSucc)) →
    P (trace ⟨k + 1, by omega⟩))

/-
A k-inductive invariant holds on all reachable states
-/
theorem k_inductive_is_invariant (P : State → Prop) (init : State → Prop)
    (next : State → State → Prop) (k : ℕ)
    (h : kInductiveInvariant P init next k) :
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      init (trace 0) →
      (∀ i : Fin n, next (trace i.castSucc) (trace i.succ)) →
      P (trace ⟨n, by omega⟩) := by
  refine' fun n => Nat.strong_induction_on n _;
  intro n ih trace hinit hnext
  by_cases hn : n ≤ k;
  · exact h.1 n hn trace hinit hnext;
  · -- Since $n > k$, we can apply the inductive step of the k-inductive invariant.
    have h_ind_step : ∀ (i : Fin (k + 1)), P (trace ⟨n - (k + 1) + i.val, by omega⟩) := by
      intro i
      specialize ih (n - (k + 1) + i.val) (by
      omega) (fun j => trace ⟨j.val, by
        linarith [ Fin.is_lt j, Fin.is_lt i, Nat.sub_add_cancel ( by linarith : k + 1 ≤ n ) ]⟩) (by
      exact hinit) (by
      exact fun j => hnext ⟨ j, by linarith [ Fin.is_lt j, Nat.sub_add_cancel ( by linarith : k + 1 ≤ n ), Fin.is_lt i ] ⟩);
      exact ih;
    have := h.2 ( fun i => trace ⟨ n - ( k + 1 ) + i.val, by omega ⟩ ) ?_ ?_ <;> simp_all +decide;
    · convert this using 2 ; simp +decide [ Nat.sub_add_cancel ( by linarith : k + 1 ≤ n ) ];
    · intro i; convert hnext ⟨ n - ( k + 1 ) + i, by omega ⟩ using 1;

-- Mining + k-induction = verified invariant
theorem mine_then_prove (P : State → Prop) (init : State → Prop)
    (next : State → State → Prop) (k : ℕ)
    (traces : List (List State))
    (_h_candidate : candidateInvariant P traces)
    (h_inductive : kInductiveInvariant P init next k) :
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      init (trace 0) →
      (∀ i : Fin n, next (trace i.castSucc) (trace i.succ)) →
      P (trace ⟨n, by omega⟩) :=
  k_inductive_is_invariant P init next k h_inductive