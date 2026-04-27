/-
Pythia.Tactic.ValidateTypesTest — exercises the `#validate_types`
LLM-defense guard on three example shapes:

1. A correct theorem (count-like name, `Nat` type) -- table emits, no
   warning.
2. An LLM-confused theorem (count-like name, `Real` type) -- table
   emits, warning fires.
3. A theorem with no count-like binders (probability-bound shape) --
   table emits, no warning.

Test discipline: each case is wrapped in a `theorem` with a trivial
proof so the file compiles. The `#validate_types` command emits log
messages; we run it and visually verify in CI / Lean Zulip that the
warnings fire exactly when expected.

ATH-725.
-/
import Mathlib
import Pythia.Tactic.ValidateTypes

namespace Pythia.ValidateTypesTest

/-! ## Case 1: count-like name with `Nat` (correct shape) -/

/-- Hoeffding-shape count statement, correctly typed `n : Nat`. -/
theorem case_nat_count_correct (n : Nat) (h : 0 < n) : 0 < n + 1 := by
  omega

#validate_types case_nat_count_correct
-- Expected:
--   logInfo: per-variable types table showing n : Nat, h : 0 < n
--   no warning


/-! ## Case 2: count-like name with `Real` (LLM-confused shape) -/

/-- Same statement shape but with `n : Real` -- the kind of LLM
type-confusion this guard is designed to catch. -/
theorem case_real_count_suspicious (n : Real) (h : 0 < n) : 0 < n + 1 := by
  linarith

#validate_types case_real_count_suspicious
-- Expected:
--   logInfo: per-variable types table showing n : Real, h : 0 < n
--   logWarning: variable 'n' is named like a count / index / size but
--              typed as `Real`. Consider `Nat`.


/-! ## Case 3: no count-like binders (genuine real-valued shape) -/

/-- Probability-bound shape: `α : Real` is genuinely a probability,
not a count. The guard should NOT warn here. -/
theorem case_real_alpha_genuine (α : Real) (h_α_pos : 0 < α) (h_α_le_one : α ≤ 1) :
    0 ≤ α := by
  linarith

#validate_types case_real_alpha_genuine
-- Expected:
--   logInfo: per-variable types table showing α : Real, h_α_pos : 0 < α,
--             h_α_le_one : α ≤ 1
--   no warning (α is not in the count-like vocabulary)


/-! ## Edge case: count-like name where `Real` is intentional -/

/-- A user could legitimately want `count : Real` for a continuous-time
arrival count. The guard's job is to FLAG, not to block; the customer
still chooses to dismiss the warning. -/
theorem case_real_count_intentional (count : Real) (h : 0 ≤ count) : 0 ≤ count + 1 := by
  linarith

#validate_types case_real_count_intentional
-- Expected:
--   logInfo: per-variable types table showing count : Real, h : 0 ≤ count
--   logWarning: variable 'count' is named like a count / index / size
--              but typed as `Real`. Consider `Nat`.

end Pythia.ValidateTypesTest
