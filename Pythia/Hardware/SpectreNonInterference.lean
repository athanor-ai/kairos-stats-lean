import Mathlib

-- Spectre-class side-channel safety (non-interference).
-- Prove that a microarchitecture does not leak secrets through
-- microarchitectural side channels (cache state, timing).
--
-- Non-interference: high-security inputs do not affect
-- low-security observable outputs.

variable {ArchState MicroState : Type*}

structure SecureProcessor (ArchState MicroState : Type*) where
  step : MicroState → MicroState
  arch_out : MicroState → ArchState  -- architectural output (visible)
  micro_obs : MicroState → ℕ         -- microarchitectural observable (timing/cache)

-- Non-interference: two executions that differ only in secret inputs
-- produce identical architectural outputs
def nonInterference (p : SecureProcessor ArchState MicroState)
    (equiv : MicroState → MicroState → Prop) : Prop :=
  ∀ s1 s2, equiv s1 s2 → p.arch_out (p.step s1) = p.arch_out (p.step s2)

-- Timing non-interference: no timing side channel
def timingNonInterference (p : SecureProcessor ArchState MicroState)
    (equiv : MicroState → MicroState → Prop) : Prop :=
  ∀ s1 s2, equiv s1 s2 → p.micro_obs (p.step s1) = p.micro_obs (p.step s2)

-- If both hold, the processor is fully non-interferent
theorem full_non_interference
    (p : SecureProcessor ArchState MicroState)
    (equiv : MicroState → MicroState → Prop)
    (h_arch : nonInterference p equiv)
    (h_timing : timingNonInterference p equiv) :
    ∀ s1 s2, equiv s1 s2 →
      p.arch_out (p.step s1) = p.arch_out (p.step s2) ∧
      p.micro_obs (p.step s1) = p.micro_obs (p.step s2) := by
  intro s1 s2 h
  exact ⟨h_arch s1 s2 h, h_timing s1 s2 h⟩

-- Fence insertion restores non-interference
-- A fence serializes execution, eliminating speculative leaks
theorem fence_restores_noninterference
    (p : SecureProcessor ArchState MicroState)
    (fence : MicroState → MicroState)
    (equiv : MicroState → MicroState → Prop)
    (_h_fence_equiv : ∀ s1 s2, equiv s1 s2 → equiv (fence s1) (fence s2))
    (h_fenced_safe : nonInterference
      { p with step := fun s => p.step (fence s) } equiv) :
    nonInterference { p with step := fun s => p.step (fence s) } equiv := by
  exact h_fenced_safe

-- N steps of non-interference compose
-- NOTE: The original statement was false at n = 0, because
-- `nonInterference` only guarantees `arch_out` equality *after*
-- applying `step`, yet `Nat.iterate p.step 0 s = s` applies no
-- step at all.  The corrected version below uses `n + 1` so that
-- at least one step is always taken.
/- Original (false) statement:
theorem n_step_noninterference
    (p : SecureProcessor ArchState MicroState)
    (equiv : MicroState → MicroState → Prop)
    (h_step : ∀ s1 s2, equiv s1 s2 → equiv (p.step s1) (p.step s2))
    (h_ni : nonInterference p equiv) :
    ∀ n s1 s2, equiv s1 s2 →
      p.arch_out (Nat.iterate p.step n s1) = p.arch_out (Nat.iterate p.step n s2) := by
  sorry
-/

/-- Corrected: after `n + 1` steps, architectural output is equal
    for equivalent initial states. -/
theorem n_step_noninterference
    (p : SecureProcessor ArchState MicroState)
    (equiv : MicroState → MicroState → Prop)
    (h_step : ∀ s1 s2, equiv s1 s2 → equiv (p.step s1) (p.step s2))
    (h_ni : nonInterference p equiv) :
    ∀ n s1 s2, equiv s1 s2 →
      p.arch_out (Nat.iterate p.step (n + 1) s1) =
      p.arch_out (Nat.iterate p.step (n + 1) s2) := by
  intro n
  induction n with
  | zero =>
    intro s1 s2 h
    simp only [Function.iterate_succ, Function.iterate_zero]
    exact h_ni s1 s2 h
  | succ n ih =>
    intro s1 s2 h
    simp only [Function.iterate_succ, Function.comp_apply] at ih ⊢
    exact ih (p.step s1) (p.step s2) (h_step s1 s2 h)
