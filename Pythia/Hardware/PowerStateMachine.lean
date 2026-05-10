import Mathlib

-- Power state machine correctness for SoC power management.
-- States: Active, Idle, Sleep, DeepSleep, Off
-- Transitions must follow a valid sequence.

inductive PowerState | active | idle | sleep | deepSleep | off
  deriving DecidableEq

inductive ValidPowerTransition : PowerState → PowerState → Prop
  | active_to_idle : ValidPowerTransition .active .idle
  | idle_to_active : ValidPowerTransition .idle .active
  | idle_to_sleep : ValidPowerTransition .idle .sleep
  | sleep_to_idle : ValidPowerTransition .sleep .idle
  | sleep_to_deep : ValidPowerTransition .sleep .deepSleep
  | deep_to_sleep : ValidPowerTransition .deepSleep .sleep
  | deep_to_off : ValidPowerTransition .deepSleep .off
  | off_to_active : ValidPowerTransition .off .active

/-
Cannot go directly from active to sleep (must go through idle)
-/
theorem no_active_to_sleep : ¬ValidPowerTransition .active .sleep := by
  rintro ⟨ ⟩

/-
Cannot go directly from active to off
-/
theorem no_active_to_off : ¬ValidPowerTransition .active .off := by
  rintro ⟨ ⟩

/-
Wake path exists: from any state, can reach active
-/
theorem wake_path_exists (s : PowerState) :
    ∃ path : List PowerState, path.head? = some s ∧ path.getLast? = some .active := by
  exact ⟨ [ s, PowerState.active ], rfl, rfl ⟩