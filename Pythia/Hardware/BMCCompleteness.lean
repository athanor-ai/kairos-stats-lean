import Mathlib

-- BMC (Bounded Model Checking) completeness and depth theorems.
-- [advisor]'s domain. Prove the relationship between BMC depth
-- and property verification completeness.

variable {State : Type*} [Fintype State]

-- BMC at depth k checks all paths of length ≤ k
def bmcSafe (init : State → Prop) (next : State → State → Prop)
    (bad : State → Prop) (k : ℕ) : Prop :=
  ∀ (n : ℕ) (trace : Fin (n + 1) → State),
    n ≤ k → init (trace 0) →
    (∀ i : Fin n, next (trace i.castSucc) (trace i.succ)) →
    ¬bad (trace ⟨n, by omega⟩)

/-
BMC is monotone in depth: safe at k implies safe at k-1
-/
omit [Fintype State] in
theorem bmc_depth_monotone (init : State → Prop) (next : State → State → Prop)
    (bad : State → Prop) (k : ℕ) :
    bmcSafe init next bad (k + 1) → bmcSafe init next bad k := by
  exact fun h n trace hn hinit hnext => h n trace ( Nat.le_succ_of_le hn ) hinit hnext

/-
BMC completeness for finite state: if safe at |S|, safe unbounded
(pigeonhole: trace of length > |S| must revisit a state)
-/
theorem bmc_finite_complete (init : State → Prop) (next : State → State → Prop)
    (bad : State → Prop) :
    bmcSafe init next bad (Fintype.card State) →
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      init (trace 0) →
      (∀ i : Fin n, next (trace i.castSucc) (trace i.succ)) →
      ¬bad (trace ⟨n, by omega⟩) := by
  intro h n
  induction' n using Nat.strong_induction_on with n ih;
  intro trace h₀ h₁ h₂;
  by_cases hn : n ≤ Fintype.card State;
  · exact h n trace hn h₀ h₁ h₂;
  · -- By the pigeonhole principle, there exist indices $i < j \leq Fintype.card State$ such that $trace i = trace j$.
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin (Fintype.card State + 1), i < j ∧ trace (Fin.castLE (by linarith) i) = trace (Fin.castLE (by linarith) j) := by
      by_contra! h;
      exact absurd ( Fintype.card_le_of_injective ( fun i : Fin ( Fintype.card State + 1 ) => trace ( Fin.castLE ( by linarith ) i ) ) fun i j hij => le_antisymm ( not_lt.1 fun hi => h _ _ hi hij.symm ) ( not_lt.1 fun hj => h _ _ hj hij ) ) ( by simp +decide );
    contrapose! ih;
    refine' ⟨ n - ( j - i ), _, _ ⟩;
    · exact Nat.sub_lt ( by linarith ) ( Nat.sub_pos_of_lt hij );
    · refine' ⟨ fun k => if hk : k.val < i.val then trace ⟨ k.val, by linarith [ Fin.is_lt k, Fin.is_lt i ] ⟩ else trace ⟨ k.val + ( j - i ), by
        omega ⟩, _, _, _ ⟩ <;> simp_all +decide;
      · cases i ; aesop;
      · intro k;
        split_ifs;
        · convert h₁ ⟨ k, by linarith [ Fin.is_lt k, Fin.is_lt i, Fin.is_lt j, Nat.sub_add_cancel ( show ( j : ℕ ) ≤ n from by linarith [ Fin.is_lt j ] ) ] ⟩ using 1;
        · convert h₁ ⟨ k, by linarith [ Fin.is_lt k, Fin.is_lt i, Fin.is_lt j, Nat.sub_add_cancel ( show ( j : ℕ ) ≥ i from le_of_lt hij ) ] ⟩ using 1;
          all_goals generalize_proofs at *;
          convert h_eq.symm using 2;
          · exact Fin.ext ( by norm_num; omega );
          · exact Fin.ext ( by norm_num; omega );
        · linarith;
        · convert h₁ ⟨ k + ( j - i ), by
            grind ⟩ using 1;
          congr 1 ; simp +decide [ add_right_comm ];
      · grind +revert

/-
Diameter bound: BMC at depth |S| is COMPLETE for finite-state systems.
This is the non-trivial claim: bounded checking at the diameter implies
unbounded safety. Uses bmc_finite_complete (the pigeonhole theorem).
-/
theorem diameter_bounded_complete (init : State → Prop) (next : State → State → Prop)
    (bad : State → Prop) :
    bmcSafe init next bad (Fintype.card State) →
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      init (trace 0) →
      (∀ i : Fin n, next (trace i.castSucc) (trace i.succ)) →
      ¬bad (trace ⟨n, by omega⟩) :=
  bmc_finite_complete init next bad