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
Fairness implies liveness under progress assumption
-/
theorem fairness_implies_liveness
    (sys : TransSys State) (P enabled : State → Prop)
    (h_progress : ∀ s s', sys.next s s' → enabled s → P s')
    (h_fair : strongFairness sys enabled P) :
    ∀ trace, isTrace sys trace →
      (∀ m, ∃ n, m ≤ n ∧ enabled (trace n)) →
      ∀ m, ∃ n, m ≤ n ∧ P (trace n) := by
  exact h_fair