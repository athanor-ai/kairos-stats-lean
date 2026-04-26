/-
Pythia.Tactic.FlagConcreteConstantsTest — regression tests for
`#flag_concrete_constants`.

## Structure

Test 1 (general theorem): a universally-quantified statement that contains
only 0 and 1. Expected: "no fixed concrete numerical constants".

Test 2 (concrete theorem): a theorem whose statement contains a hard-coded
constant >= 2. Expected: the info message listing that constant.

Test 3 (mixed): a theorem whose statement contains both universally-quantified
variables and hard-coded constants. Expected: the constants are reported while
the variables are not.

All tests compile cleanly; `#flag_concrete_constants` emits `logInfo` only
and never blocks elaboration.

Note: theorem names must be non-private so they are accessible via their
fully-qualified namespace from the `#flag_concrete_constants` command.
-/
import Pythia.Tactic.FlagConcreteConstants

namespace Pythia.FlagConcreteConstantsTest

-- A general (good) theorem: only uses 0 and 1, which are exempt.
-- Expected: "no fixed concrete numerical constants"
theorem generalBound (n : Nat) (h : 0 < n) : 1 <= n :=
  h

-- Test 1: general statement, expect clean pass.
#flag_concrete_constants Pythia.FlagConcreteConstantsTest.generalBound

-- An arithmetic identity with hard-coded constants 5 and 100 in the statement.
-- Expected: info message reporting 5 and 100.
theorem concreteExample : 5 + 100 = 105 :=
  rfl

-- Test 2: concrete constants, expect them to be reported.
#flag_concrete_constants Pythia.FlagConcreteConstantsTest.concreteExample

-- A theorem with mixed quantified and concrete parameters.
-- `n` is universally quantified; 42 is hard-coded in the statement.
-- Expected: 42 is reported; `n` is not.
theorem mixedExample (n : Nat) : n + 42 = 42 + n :=
  Nat.add_comm n 42

-- Test 3: only the concrete 42 should be flagged.
#flag_concrete_constants Pythia.FlagConcreteConstantsTest.mixedExample

end Pythia.FlagConcreteConstantsTest
