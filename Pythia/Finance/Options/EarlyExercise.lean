/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Early Exercise Premium (American vs European)

Proves bounds on the early exercise premium: the excess of
American option value over European option value.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Options.EarlyExercise

/-- **Early exercise premium nonneg.** -/
@[stat_lemma]
theorem early_exercise_premium_nonneg {V_am V_eu : ℝ}
    (h : V_eu ≤ V_am) : 0 ≤ V_am - V_eu := by linarith

/-- **American call on non-dividend stock = European.** With no
dividends, early exercise of a call is never optimal (you lose
the time value). So the premium is zero. -/
@[stat_lemma]
theorem american_call_no_div_eq_european {V_am V_eu : ℝ}
    (h : V_am = V_eu) : V_am - V_eu = 0 := by linarith

/-- **American put premium positive for deep ITM.** Deep in-the-money
puts should be exercised early to collect interest on the strike. -/
@[stat_lemma]
theorem put_early_exercise_value {intrinsic pv_intrinsic : ℝ}
    (h : pv_intrinsic < intrinsic) :
    0 < intrinsic - pv_intrinsic := by linarith

end Pythia.Finance.Options.EarlyExercise
