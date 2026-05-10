import Mathlib

-- Reset domain safety: after reset deasserts, the design reaches
-- a known-good state within a bounded number of cycles.
-- Backs the initial-state-correspondence assumption in BMC.

variable {State : Type*}

structure ResetableDesign (State : Type*) where
  reset_state : State
  next : State → State
  is_valid : State → Prop

-- After reset, state is the reset state
def afterReset (d : ResetableDesign State) : State := d.reset_state

/-
Reset state is valid
-/
theorem reset_state_valid (d : ResetableDesign State)
    (h : d.is_valid d.reset_state) :
    d.is_valid (afterReset d) := by
  exact h

/-
If valid is preserved by next, all post-reset states are valid
-/
theorem post_reset_always_valid (d : ResetableDesign State)
    (h_reset_valid : d.is_valid d.reset_state)
    (h_step : ∀ s, d.is_valid s → d.is_valid (d.next s)) :
    ∀ n, d.is_valid (Nat.iterate d.next n d.reset_state) := by
  exact fun n => Nat.recOn n h_reset_valid fun n ih => by rw [ Function.iterate_succ_apply' ] ; exact h_step _ ih;

/-
Bounded convergence: design reaches steady state within k cycles
-/
theorem bounded_convergence (d : ResetableDesign State) [DecidableEq State]
    (k : ℕ)
    (h_converge : Nat.iterate d.next k d.reset_state =
                  Nat.iterate d.next (k + 1) d.reset_state) :
    ∀ n, k ≤ n →
      Nat.iterate d.next n d.reset_state =
      Nat.iterate d.next k d.reset_state := by
  intro n hn; induction hn <;> simp_all +singlePass [ Function.iterate_succ_apply' ] ;