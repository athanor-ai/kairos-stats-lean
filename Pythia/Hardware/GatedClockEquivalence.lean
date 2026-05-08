/-
Pythia.Hardware.GatedClockEquivalence — functional equivalence of
clock-gated registers under Annapurna RTL power-optimization.

Clock gating is the most common power-reduction technique in
Annapurna RTL: a clock gate disables the clock to a register when
its value will not change, avoiding a spurious flip-flop toggle and
the associated dynamic power.  This module provides a machine-checked
proof that a gated design is functionally identical to a gold
(un-gated) reference, provided the enable signal is asserted whenever
the register value would change.

Four theorems are established:

  1. clock_gate_equiv_when_enabled   — when enable = true, both
       designs advance to the same next state.
  2. clock_gate_hold_when_disabled   — when enable = false, the gated
       design retains its current value (no spurious transition).
  3. clock_gate_functional_equiv     — if enable is true whenever
       next ≠ current, the two designs produce identical output
       sequences for all time steps.
  4. clock_gate_power_safe           — clock gating never introduces
       new output transitions that were absent in the gold design.
-/

import Mathlib

namespace Pythia.Hardware.GatedClockEquivalence

-- ---------------------------------------------------------------------------
-- State-machine model
-- ---------------------------------------------------------------------------

/-- Abstract register state over an arbitrary value type α. -/
@[ext]
structure RegState (α : Type*) where
  value : α

/-- Gold (un-gated) design: register updates unconditionally each cycle. -/
def goldStep {α : Type*} (next_val : α) : RegState α :=
  { value := next_val }

/-- Gated design: register updates only when enable = true;
    otherwise it holds its previous value. -/
def gatedStep {α : Type*} (enable : Bool) (next_val : α) (cur : RegState α) :
    RegState α :=
  if enable then { value := next_val } else cur

-- ---------------------------------------------------------------------------
-- Theorem 1 — equivalence when enabled
-- ---------------------------------------------------------------------------

/-- When the enable signal is asserted, the gated register produces the
    same next state as the un-gated gold design. -/
theorem clock_gate_equiv_when_enabled
    {α : Type*} (next_val : α) (cur : RegState α) :
    gatedStep true next_val cur = goldStep next_val := by
  simp [gatedStep, goldStep]

-- ---------------------------------------------------------------------------
-- Theorem 2 — hold when disabled
-- ---------------------------------------------------------------------------

/-- When the enable signal is de-asserted, the gated register retains
    its current value unchanged. -/
theorem clock_gate_hold_when_disabled
    {α : Type*} (next_val : α) (cur : RegState α) :
    gatedStep false next_val cur = cur := by
  simp [gatedStep]

-- ---------------------------------------------------------------------------
-- Sequential trace model
-- ---------------------------------------------------------------------------

/-- An environment supplies, at each time step, the combinational
    next-value and the enable signal.  The gold and gated designs
    are both driven by the same environment. -/
structure Env (α : Type*) where
  next_val : ℕ → α
  enable   : ℕ → Bool

/-- Gold trace: state at every time step under un-gated semantics. -/
noncomputable def goldTrace {α : Type*} (env : Env α) (init : RegState α) :
    ℕ → RegState α
  | 0     => init
  | t + 1 => goldStep (env.next_val t)

/-- Gated trace: state at every time step under clock-gated semantics. -/
noncomputable def gatedTrace {α : Type*} (env : Env α) (init : RegState α) :
    ℕ → RegState α
  | 0     => init
  | t + 1 => gatedStep (env.enable t) (env.next_val t) (gatedTrace env init t)

-- ---------------------------------------------------------------------------
-- Theorem 3 — functional equivalence of full traces
-- ---------------------------------------------------------------------------

/-- The invariant used in the induction: after t steps the gated and
    gold traces agree, and moreover the gated state equals the value
    that was last committed by the gold design.

    Concretely, at step 0 both are `init`.  For t > 0, the gold trace
    is determined only by `env.next_val (t-1)` (it forgets history),
    while the gated trace may hold an earlier value.  The enable
    condition `next ≠ current → enable = true` guarantees that
    whenever the gold design would differ from the current gated state,
    the gate is open and both designs move to the same new value.

    We prove the slightly stronger statement that the two traces are
    pointwise equal, which is exactly what we need. -/
theorem clock_gate_functional_equiv
    {α : Type*} [DecidableEq α]
    (env : Env α)
    (init : RegState α)
    (h_enable : ∀ t : ℕ,
      env.next_val t ≠ (gatedTrace env init t).value →
      env.enable t = true) :
    ∀ t : ℕ, gatedTrace env init t = goldTrace env init t := by
  intro t
  induction t with
  | zero =>
    -- Both traces start at init
    simp [gatedTrace, goldTrace]
  | succ n ih =>
    -- Unfold one step of both traces
    show gatedStep (env.enable n) (env.next_val n) (gatedTrace env init n) =
         goldStep (env.next_val n)
    -- Case split on enable at step n
    by_cases he : env.enable n = true
    · -- Gate is open: gated advances to next_val n, same as gold
      simp [gatedStep, goldStep, he]
    · -- Gate is closed: gated holds current value
      simp only [Bool.not_eq_true] at he
      -- By the enable invariant, next_val n must equal current gated value
      have hval_eq : env.next_val n = (gatedTrace env init n).value := by
        by_contra hne
        exact absurd (h_enable n hne) (by simp [he])
      -- gated holds current value = env.next_val n = gold's output
      simp only [gatedStep, he]
      simp only [goldStep]
      -- need: gatedTrace env init n = { value := env.next_val n }
      ext
      simp [hval_eq]

-- ---------------------------------------------------------------------------
-- Theorem 4 — power safety (no new transitions)
-- ---------------------------------------------------------------------------

/-- Clock gating never introduces a new output transition that was
    absent in the gold design.  Formally: if the gated trace changes
    between step t and step t+1, the gold trace also changes. -/
theorem clock_gate_power_safe
    {α : Type*} [DecidableEq α]
    (env : Env α)
    (init : RegState α)
    (h_enable : ∀ t : ℕ,
      env.next_val t ≠ (gatedTrace env init t).value →
      env.enable t = true)
    (t : ℕ)
    (h_gate_changes :
      (gatedTrace env init (t + 1)).value ≠ (gatedTrace env init t).value) :
    (goldTrace env init (t + 1)).value ≠ (goldTrace env init t).value := by
  -- Rewrite both traces using the equivalence theorem
  have heq := clock_gate_functional_equiv env init h_enable
  rw [← heq (t + 1), ← heq t]
  exact h_gate_changes

end Pythia.Hardware.GatedClockEquivalence
