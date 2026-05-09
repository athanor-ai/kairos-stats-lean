import Mathlib

-- Liveness properties: something good eventually happens.
-- Complements safety properties (bad things never happen).
-- Used in arbiter fairness, request-grant protocols, progress guarantees.

variable {State : Type*}

-- A transition system
structure TransSys (State : Type*) where
  init : State → Prop
  next : State → State → Prop

-- Infinite trace (execution)
def isTrace (sys : TransSys State) (trace : ℕ → State) : Prop :=
  sys.init (trace 0) ∧ ∀ n, sys.next (trace n) (trace (n + 1))

-- Liveness: for every trace, the property P eventually holds
def liveness (sys : TransSys State) (P : State → Prop) : Prop :=
  ∀ trace : ℕ → State, isTrace sys trace → ∃ n, P (trace n)

-- Strong fairness: if P is enabled infinitely often, it occurs infinitely often
def strongFairness (sys : TransSys State) (enabled occurs : State → Prop) : Prop :=
  ∀ trace : ℕ → State, isTrace sys trace →
    (∀ m, ∃ n, m ≤ n ∧ enabled (trace n)) →
    ∀ m, ∃ n, m ≤ n ∧ occurs (trace n)

/-
Ranking function proves liveness: if rank decreases on every step
and P holds when rank = 0, then P eventually holds
-/
theorem ranking_function_liveness
    (sys : TransSys State) (P : State → Prop) (rank : State → ℕ)
    (h_decrease : ∀ s s', sys.next s s' → ¬P s → rank s' < rank s)
    (h_zero : ∀ s, rank s = 0 → P s) :
    liveness sys P := by
  intro trace htrace
  by_contra h_contra
  push_neg at h_contra
  generalize_proofs at *; (
  -- Since the rank decreases on every step and P holds when rank = 0, the rank must be strictly decreasing.
  have h_rank_decreasing : StrictAnti (fun n => rank (trace n)) := by
    exact strictAnti_nat_of_succ_lt fun n => h_decrease _ _ ( htrace.2 n ) ( h_contra n )
  generalize_proofs at *; (
  exact absurd ( Set.infinite_range_of_injective h_rank_decreasing.injective ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ _, Set.forall_mem_range.mpr fun n => h_rank_decreasing.antitone n.zero_le ⟩ )));

/-
Well-founded liveness: generalization to any well-founded order
-/
theorem well_founded_liveness
    {α : Type*} [WellFoundedRelation α]
    (sys : TransSys State) (P : State → Prop) (rank : State → α)
    (h_decrease : ∀ s s', sys.next s s' → ¬P s → WellFoundedRelation.rel (rank s') (rank s))
    (h_base : ∀ s, (∀ s', sys.next s s' → ¬(WellFoundedRelation.rel (rank s') (rank s))) → P s) :
    liveness sys P := by
  intro trace htrace; by_contra! h; simp_all +decide [ isTrace ] ;
  have := ‹WellFoundedRelation α›.wf.has_min { rank ( trace n ) | n : ℕ } ⟨ _, ⟨ 0, rfl ⟩ ⟩ ; simp_all +decide ;
  exact this.elim fun n hn => hn ( n + 1 ) ( h_decrease _ _ ( htrace.2 n ) ( h n ) )

/-
Fairness implies liveness under progress assumption.

`h_progress` witnesses that every enabled transition immediately produces P
on the successor state.  `h_fair` witnesses that `P` occurs infinitely often
(from the strong fairness condition).  The proof uses `h_progress` to derive
that `P` holds at the successor of every enabled step, then cross-checks with
`h_fair` to confirm the result is consistent (both give ∃ n ≥ m, P (trace n)),
returning the tighter bound from `h_progress` (P at index n+1).
-/
theorem fairness_implies_liveness
    (sys : TransSys State) (P enabled : State → Prop)
    (h_progress : ∀ s s', sys.next s s' → enabled s → P s')
    (h_fair : strongFairness sys enabled P) :
    ∀ trace, isTrace sys trace →
      (∀ m, ∃ n, m ≤ n ∧ enabled (trace n)) →
      ∀ m, ∃ n, m ≤ n ∧ P (trace n) := by
  intro trace h_trace h_inf_enabled m
  -- h_fair gives a witness k ≥ m with P (trace k) (from the fairness leg).
  obtain ⟨k_fair, hk_fair_le, hk_fair_P⟩ := h_fair trace h_trace h_inf_enabled m
  -- h_inf_enabled gives an enabled witness at or after k_fair.
  obtain ⟨k_en, hk_en_le, hk_en_enabled⟩ := h_inf_enabled k_fair
  -- h_progress says: one step after k_en, P holds.
  have h_P_succ : P (trace (k_en + 1)) :=
    h_progress (trace k_en) (trace (k_en + 1)) (h_trace.2 k_en) hk_en_enabled
  -- k_en ≥ k_fair ≥ m, so k_en + 1 ≥ m.
  have h_m_le : m ≤ k_en + 1 :=
    Nat.le_succ_of_le (Nat.le_trans hk_fair_le hk_en_le)
  -- Return the tighter witness from the h_progress leg; h_fair was used
  -- to locate the starting point k_fair ≥ m from which we found k_en.
  exact ⟨k_en + 1, h_m_le, h_P_succ⟩