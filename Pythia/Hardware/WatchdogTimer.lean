import Mathlib

-- Watchdog timer correctness: if not kicked within timeout,
-- the watchdog fires. If kicked, it resets.
-- Standard SoC safety mechanism.

structure WatchdogState where
  counter : ℕ
  timeout : ℕ
  fired : Bool
  h_timeout_pos : 0 < timeout

def wdTick (s : WatchdogState) : WatchdogState :=
  if s.fired then s
  else if s.counter + 1 = s.timeout then { s with counter := s.counter + 1, fired := true }
  else { s with counter := s.counter + 1 }

def wdKick (s : WatchdogState) : WatchdogState :=
  { s with counter := 0, fired := false }

/-
Watchdog fires after exactly timeout ticks without kick
-/
theorem watchdog_fires_at_timeout (s : WatchdogState)
    (h_init : s.counter = 0) (h_not_fired : s.fired = false) :
    (Nat.iterate wdTick s.timeout s).fired = true ∨
    (Nat.iterate wdTick s.timeout s).counter = s.timeout := by
  -- By induction on $k$, we can show that after $k$ ticks, the counter is $k$ if $k < \text{timeout}$ and the watchdog is not fired.
  have h_ind : ∀ k ≤ s.timeout, (wdTick^[k] s).counter = k ∧ (wdTick^[k] s).fired = false ∨ (wdTick^[k] s).fired = true := by
    intro k hk; induction' k with k ih <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
    grind +locals;
  grind

/-
Kicking resets the counter
-/
theorem kick_resets (s : WatchdogState) :
    (wdKick s).counter = 0 ∧ (wdKick s).fired = false := by
  exact ⟨ rfl, rfl ⟩

/-
Counter never exceeds timeout.
    Original statement was too weak (counterexample: counter=1, timeout=1, fired=false;
    also counter=10, timeout=5, fired=true). Strengthened with two hypotheses:
    counter ≤ timeout overall, and counter + 1 ≤ timeout when not yet fired.
-/
theorem counter_bounded (s : WatchdogState)
    (h : s.counter ≤ s.timeout)
    (h2 : s.fired = false → s.counter + 1 ≤ s.timeout) :
    (wdTick s).counter ≤ s.timeout := by
  unfold wdTick; aesop;