import Mathlib

-- Sequential equivalence via k-induction on a miter circuit.
-- This is the core reasoning pattern EBMC uses for FIFO/register verification.
-- Prove: if a property holds at init and is preserved by one step,
-- then it holds for all reachable states (unbounded induction).

variable {State Input : Type*}

structure SeqCircuit (State Input : Type*) where
  init : State
  next : State → Input → State

def reachable (c : SeqCircuit State Input) : (n : ℕ) → (Fin n → Input) → State
  | 0, _ => c.init
  | k + 1, inputs => c.next (reachable c k (inputs ∘ Fin.castSucc)) (inputs ⟨k, by omega⟩)

/-
k-induction base: property holds at init
k-induction step: property preserved by next
Conclusion: property holds at all reachable states

1-induction (standard induction)
-/
theorem one_induction (c : SeqCircuit State Input) (P : State → Prop)
    (h_base : P c.init)
    (h_step : ∀ s : State, P s → ∀ i : Input, P (c.next s i)) :
    ∀ (n : ℕ) (inputs : Fin n → Input), P (reachable c n inputs) := by
  -- We'll use induction on n to prove the statement.
  intro n
  induction' n with k ih;
  · exact fun _ => h_base;
  · exact fun inputs => h_step _ ( ih _ ) _

/-
k-induction: if property holds for first k states AND
k consecutive true states imply the next is true,
then it holds for all states
-/
theorem k_induction (c : SeqCircuit State Input) (P : State → Prop)
    (k : ℕ) (hk : 0 < k)
    (h_base : ∀ (n : ℕ) (_hn : n < k) (inputs : Fin n → Input),
      P (reachable c n inputs))
    (h_step : ∀ (n : ℕ) (inputs : Fin (n + k + 1) → Input),
      (∀ (j : ℕ) (_hj : j < k), P (reachable c (n + j) (fun i => inputs ⟨i, by omega⟩))) →
      P (reachable c (n + k) (fun i => inputs ⟨i, by omega⟩))) :
    ∀ (n : ℕ) (inputs : Fin n → Input), P (reachable c n inputs) := by
  -- We prove this theorem by strong induction on $n$.
  intro n
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn : n < k;
  · exact h_base n hn;
  · -- Since $n \geq k$, we can write $n = (n - k) + k$.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + k := by
      exact ⟨ n - k, by rw [ Nat.sub_add_cancel ( le_of_not_gt hn ) ] ⟩;
    intro inputs;
    convert h_step m ( Fin.snoc inputs ( inputs ⟨ m + k - 1, Nat.sub_lt ( by linarith ) zero_lt_one ⟩ ) ) _ using 1;
    · simp +decide [ Fin.snoc ];
    · grind

-- Miter equivalence: two circuits produce same output
-- if their miter (XOR of outputs) is always 0
variable {α : Type*}

theorem miter_equiv (c1 c2 : SeqCircuit State Input)
    (out : State → α) [DecidableEq α]
    (h_init : out c1.init = out c2.init)
    (h_step : ∀ s1 s2 : State, out s1 = out s2 →
      ∀ i : Input, out (c1.next s1 i) = out (c2.next s2 i)) :
    ∀ (n : ℕ) (inputs : Fin n → Input),
      out (reachable c1 n inputs) = out (reachable c2 n inputs) := by
  intro n;
  induction' n with n ih;
  · exact fun _ => h_init;
  · exact fun inputs => h_step _ _ ( ih _ ) _