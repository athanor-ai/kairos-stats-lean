import Mathlib

-- IC3/PDR (Property-Directed Reachability) Soundness.
-- Bradley 2011. The algorithm behind modern model checkers.
-- Prove that if IC3 returns SAFE, the property holds on all reachable states.

variable {State : Type*} [DecidableEq State]

-- Transition system
structure IC3System (State : Type*) where
  init : State → Prop
  next : State → State → Prop
  bad  : State → Prop

-- Frame sequence: F_0 ⊇ F_1 ⊇ ... ⊇ F_k where F_0 = Init
-- Each frame overapproximates states reachable in ≤ i steps
structure FrameSeq (State : Type*) (k : ℕ)
    (init : State → Prop) (next : State → State → Prop) (bad : State → Prop) where
  frames : Fin (k + 1) → (State → Prop)
  -- F_0 contains all initial states
  init_in_F0 : ∀ s, init s → frames 0 s
  -- Frames are monotonically decreasing
  monotone : ∀ i j : Fin (k + 1), i ≤ j → ∀ s, frames j s → frames i s
  -- Each frame is inductive relative to the next
  consecution : ∀ (i : Fin k) (s s' : State),
    frames i.castSucc s → next s s' → frames i.succ s'
  -- No bad states in any frame
  no_bad : ∀ (i : Fin (k + 1)) (s : State), frames i s → ¬bad s

/-
Helper: a valid trace of length n ≤ k has trace(n) ∈ F_n
-/
omit [DecidableEq State] in
lemma trace_in_frame
    (sys : IC3System State) (k : ℕ)
    (fs : FrameSeq State k sys.init sys.next sys.bad)
    (n : ℕ) (hn : n ≤ k)
    (trace : Fin (n + 1) → State)
    (h_init : sys.init (trace 0))
    (h_step : ∀ i : Fin n, sys.next (trace i.castSucc) (trace i.succ)) :
    ∀ (j : ℕ) (hj : j ≤ n),
      fs.frames ⟨j, by omega⟩ (trace ⟨j, by omega⟩) := by
  intro j hj
  induction' j with j ih;
  · exact fs.init_in_F0 _ h_init;
  · convert fs.consecution ⟨ j, by linarith ⟩ _ _ ( ih ( Nat.le_of_succ_le hj ) ) ( h_step ⟨ j, by linarith ⟩ ) using 1

/-
IC3 soundness: if a valid frame sequence exists, the property holds
on all reachable states (no bad state is reachable)
-/
omit [DecidableEq State] in
theorem ic3_soundness
    (sys : IC3System State) (k : ℕ)
    (fs : FrameSeq State k sys.init sys.next sys.bad) :
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      sys.init (trace 0) →
      (∀ i : Fin n, sys.next (trace i.castSucc) (trace i.succ)) →
      n ≤ k →
      ¬sys.bad (trace ⟨n, Nat.lt_succ_iff.mpr (le_refl n)⟩) := by
  exact fun n trace h₀ h₁ h₂ => fs.no_bad _ _ ( trace_in_frame sys k fs n h₂ trace h₀ h₁ n le_rfl )

/-
Fixed point: if F_i = F_{i+1}, then F_i is inductive
-/
omit [DecidableEq State] in
lemma fixed_point_inductive
    (sys : IC3System State) (k : ℕ)
    (fs : FrameSeq State k sys.init sys.next sys.bad)
    (i : Fin k)
    (h_fixed : ∀ s, fs.frames i.castSucc s ↔ fs.frames i.succ s)
    (s s' : State)
    (hs : fs.frames i.succ s)
    (ht : sys.next s s') :
    fs.frames i.succ s' := by
  exact fs.consecution i s s' ( h_fixed s |>.2 hs ) ht

/-
Helper: once in the fixed-point frame, all subsequent trace states stay there
-/
omit [DecidableEq State] in
lemma trace_stays_in_fixed_frame
    (sys : IC3System State) (k : ℕ)
    (fs : FrameSeq State k sys.init sys.next sys.bad)
    (i : Fin k)
    (h_fixed : ∀ s, fs.frames i.castSucc s ↔ fs.frames i.succ s)
    (n : ℕ) (trace : Fin (n + 1) → State)
    (h_step : ∀ j : Fin n, sys.next (trace j.castSucc) (trace j.succ))
    (start : ℕ) (hs : start ≤ n)
    (h_start : fs.frames i.succ (trace ⟨start, by omega⟩)) :
    ∀ (j : ℕ) (_ : start ≤ j) (hj' : j ≤ n),
      fs.frames i.succ (trace ⟨j, by omega⟩) := by
  -- We proceed by induction on $j$ starting from $start$.
  intro j hj_ge_start hj_le_n
  induction' hj_ge_start with j _ ih;
  · exact h_start;
  · exact fixed_point_inductive sys k fs i h_fixed _ _ ( by solve_by_elim [ Nat.le_of_succ_le ] ) ( h_step ⟨ j, hj_le_n ⟩ )

/-
Fixed point detection: if F_i = F_{i+1}, the property holds UNBOUNDED
-/
omit [DecidableEq State] in
theorem ic3_fixed_point_unbounded
    (sys : IC3System State) (k : ℕ)
    (fs : FrameSeq State k sys.init sys.next sys.bad)
    (i : Fin k)
    (h_fixed : ∀ s, fs.frames i.castSucc s ↔ fs.frames i.succ s) :
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      sys.init (trace 0) →
      (∀ j : Fin n, sys.next (trace j.castSucc) (trace j.succ)) →
      ¬sys.bad (trace ⟨n, Nat.lt_succ_iff.mpr (le_refl n)⟩) := by
  intro n trace h_init h_step;
  by_cases hn : n ≤ k;
  · exact ic3_soundness sys k fs n trace h_init h_step hn;
  · -- Since $n > k$, we can apply the fixed point detection lemma to get that $trace(i.succ.val) ∈ F_{i.succ}$.
    have h_trace_succ : fs.frames i.succ (trace ⟨i.val + 1, by
      linarith [ Fin.is_lt i ]⟩) := by
      have := trace_in_frame sys k fs ( i.val + 1 ) ( by linarith [ Fin.is_lt i ] ) ( fun j => trace ⟨ j, by linarith [ Fin.is_lt i, j.2 ] ⟩ ) h_init ( fun j => h_step ⟨ j, by linarith [ Fin.is_lt i, j.2 ] ⟩ ) ( i.val + 1 ) ( by linarith ) ; aesop;
    generalize_proofs at *;
    exact fs.no_bad _ _ ( trace_stays_in_fixed_frame sys k fs i h_fixed n trace h_step ( i.val + 1 ) ( by linarith [ Fin.is_lt i ] ) h_trace_succ n ( by linarith [ Fin.is_lt i ] ) ( by linarith [ Fin.is_lt i ] ) )