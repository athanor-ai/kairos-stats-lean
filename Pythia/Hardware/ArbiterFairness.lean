import Mathlib

open Finset BigOperators

-- Round-robin arbiter: N requestors, grants cycle through in order.
-- Fairness: no requestor starves if it keeps requesting.

structure ArbiterState (N : ℕ) where
  lastGrant : Fin N

def nextGrant (N : ℕ) (s : ArbiterState N) (requests : Fin N → Bool) : Option (Fin N) :=
  let _start := s.lastGrant.val + 1
  Finset.univ.filter (fun i : Fin N => requests i == true) |>.min

noncomputable def roundRobinNext (N : ℕ) (_hN : 0 < N) (s : ArbiterState N)
    (requests : Fin N → Bool) : ArbiterState N :=
  let candidates := Finset.univ.filter (fun i : Fin N => requests i)
  if hc : candidates.Nonempty then
    let afterLast := candidates.filter (fun i => s.lastGrant.val < i.val)
    let winner := if h2 : afterLast.Nonempty then afterLast.min' h2
                  else candidates.min' hc
    { lastGrant := winner }
  else s

-- Simpler model: just track grant sequence
noncomputable def grantSeq (N : ℕ) (hN : 1 < N)
    (requests : ℕ → Fin N → Bool) : ℕ → Fin N
  | 0 => ⟨0, by omega⟩
  | t + 1 =>
    let prev := grantSeq N hN requests t
    let candidates := Finset.univ.filter (fun i : Fin N => requests t i)
    if h : candidates.Nonempty then
      let afterPrev := candidates.filter (fun i => prev.val < i.val)
      if h2 : afterPrev.Nonempty then afterPrev.min' h2
      else candidates.min' h
    else prev

/-! ## Helper lemmas for no_starvation -/

/-
Candidates are nonempty when i requests
-/
private lemma candidates_nonempty {N : ℕ} (requests : Fin N → Bool) (i : Fin N)
    (hi : requests i = true) :
    (Finset.univ.filter (fun j : Fin N => requests j)).Nonempty := by
  exact ⟨ i, by simpa using hi ⟩

-- Cyclic distance from g to i (mod N)
private noncomputable def cdist {N : ℕ} (g i : Fin N) : ℕ :=
  if g.val ≤ i.val then i.val - g.val else N - g.val + i.val

private lemma cdist_eq_zero_iff {N : ℕ} (g i : Fin N) :
    cdist g i = 0 ↔ g = i := by
  unfold cdist;
  grind

private lemma cdist_lt_N {N : ℕ} (hN : 1 < N) (g i : Fin N) :
    cdist g i < N := by
  unfold cdist; split_ifs <;> omega;

/-
Case 1: prev.val < i.val → next grant has val in (prev.val, i.val]
-/
private lemma grantSeq_step_below {N : ℕ} (hN : 1 < N)
    (requests : ℕ → Fin N → Bool) (i : Fin N) (t : ℕ)
    (h_req : requests t i = true)
    (prev : Fin N) (hprev : prev = grantSeq N hN requests t)
    (hlt : prev.val < i.val) :
    let g' := grantSeq N hN requests (t + 1)
    prev.val < g'.val ∧ g'.val ≤ i.val := by
  rw [ grantSeq ];
  split_ifs <;> simp_all +decide [ Finset.min' ];
  split_ifs <;> simp_all +decide [ Finset.inf'_le, Finset.le_inf' ];
  · exact ⟨ i, ⟨ h_req, hlt ⟩, le_rfl ⟩;
  · grind

/-
Case 2: prev.val > i.val → next grant either increases or wraps to ≤ i.val
-/
private lemma grantSeq_step_above {N : ℕ} (hN : 1 < N)
    (requests : ℕ → Fin N → Bool) (i : Fin N) (t : ℕ)
    (h_req : requests t i = true)
    (prev : Fin N) (hprev : prev = grantSeq N hN requests t)
    (hgt : prev.val > i.val) :
    let g' := grantSeq N hN requests (t + 1)
    g'.val > prev.val ∨ g'.val ≤ i.val := by
  simp +decide [ grantSeq ];
  split_ifs <;> simp_all +decide [ Finset.min' ];
  exact Or.inr ⟨ i, h_req, le_rfl ⟩

/-
Combined: cdist decreases at each step
-/
private lemma cdist_decreases {N : ℕ} (hN : 1 < N)
    (requests : ℕ → Fin N → Bool) (i : Fin N)
    (h_req : ∀ t, requests t i = true) (t : ℕ)
    (hne : grantSeq N hN requests t ≠ i) :
    cdist (grantSeq N hN requests (t + 1)) i < cdist (grantSeq N hN requests t) i := by
  by_cases hlt : grantSeq N hN requests t < i;
  · -- By grantSeq_step_below, we have prev.val < g'.val ∧ g'.val ≤ i.val.
    have h_step_below : let g' := grantSeq N hN requests (t + 1); (grantSeq N hN requests t).val < g'.val ∧ g'.val ≤ i.val := by
      apply grantSeq_step_below hN requests i t (h_req t) (grantSeq N hN requests t) rfl hlt;
    unfold cdist; split_ifs <;> omega;
  · by_cases hgt : grantSeq N hN requests t > i;
    · have := grantSeq_step_above hN requests i t ( h_req t ) ( grantSeq N hN requests t ) rfl hgt;
      unfold cdist;
      split_ifs <;> omega;
    · exact False.elim <| hne <| le_antisymm ( le_of_not_gt hgt ) ( le_of_not_gt hlt )

/-
No starvation: if requestor i requests at every step, it gets granted within N steps
-/
theorem no_starvation (N : ℕ) (hN : 1 < N)
    (requests : ℕ → Fin N → Bool)
    (i : Fin N)
    (h_always_requests : ∀ t, requests t i = true)
    (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ t ≤ t₀ + N ∧ grantSeq N hN requests t = i := by
  by_contra! h;
  -- By induction on $k$, show that $cdist (grantSeq N hN requests (t₀ + k)) i ≤ cdist (grantSeq N hN requests t₀) i - k$ for all $k ≤ N$.
  have h_ind : ∀ k ≤ N, cdist (grantSeq N hN requests (t₀ + k)) i ≤ cdist (grantSeq N hN requests t₀) i - k := by
    intro k hk_le_N; induction' k with k ih <;> simp_all +decide [ Nat.succ_eq_add_one, ← add_assoc ] ;
    exact Nat.le_sub_one_of_lt ( lt_of_lt_of_le ( cdist_decreases hN requests i h_always_requests ( t₀ + k ) ( h _ ( by linarith ) ( by linarith ) ) ) ( ih ( by linarith ) ) );
  specialize h_ind N le_rfl ; simp_all +decide [ cdist_eq_zero_iff ];
  exact absurd h_ind ( by rw [ Nat.sub_eq_zero_of_le ( by linarith [ cdist_lt_N hN ( grantSeq N hN requests t₀ ) i ] ) ] ; exact Nat.not_le_of_gt ( Nat.pos_of_ne_zero ( by simpa [ cdist_eq_zero_iff ] using h ( t₀ + N ) ( by linarith ) ( by linarith ) ) ) )

/-! ## Grant validity -/

-- Grant goes to a requestor (not to someone who didn't request)
theorem grant_valid (N : ℕ) (hN : 1 < N)
    (requests : ℕ → Fin N → Bool) (t : ℕ)
    (h : (Finset.univ.filter (fun i : Fin N => requests t i)).Nonempty) :
    requests t (grantSeq N hN requests (t + 1)) = true := by
  unfold grantSeq;
  simp +zetaDelta at *;
  split_ifs ; simp_all +decide [ Finset.min' ];
  · convert Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 |> Finset.mem_filter.mp |>.2;
  · exact Finset.mem_filter.mp ( Finset.min'_mem _ <| by simpa using h ) |>.2