/-
Pythia.Tactic.MinimizeHypothesesTest — regression tests for
`#minimize_hypotheses`.

## Structure

Test 1 (all used): a theorem where every hypothesis appears in the proof body.
Expected: "all N hypotheses used".

Test 2 (one unused): a theorem with one obviously-unused hypothesis
`(_unused : True)`. Expected: _unused is reported [UNUSED].

Test 3 (partial use): a theorem with three hypotheses where the proof uses
only two. Expected: the unreferenced hypothesis is reported [UNUSED].

All tests compile cleanly; `#minimize_hypotheses` emits `logInfo` only
and never blocks elaboration.

Note: theorem names must be non-private so they are accessible via their
fully-qualified namespace from the `#minimize_hypotheses` command.
-/
import Pythia.Tactic.MinimizeHypotheses

namespace Pythia.MinimizeHypothesesTest

-- Test 1: all hypotheses are used.
-- `a`, `b`, and `h` all appear in the proof body.
-- Expected: all 3 hypotheses used.
theorem allUsed (a b : Nat) (h : a < b) : a < b + 1 :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right b 1)

#minimize_hypotheses Pythia.MinimizeHypothesesTest.allUsed

-- Test 2: one obviously-unused hypothesis.
-- `_unused : True` never appears in the proof body.
-- Expected: _unused is [UNUSED], n is [USED].
theorem oneUnused (n : Nat) (_unused : True) : n + 0 = n :=
  Nat.add_zero n

#minimize_hypotheses Pythia.MinimizeHypothesesTest.oneUnused

-- Test 3: three hypotheses, only two used in the proof.
-- `a` and `hab` are referenced; `hbc` is not (we only need a < b, not b < c).
-- Expected: hbc is [UNUSED].
theorem partialUse (a b c : Nat) (hab : a < b) (_hbc : b < c) : a < b :=
  hab

#minimize_hypotheses Pythia.MinimizeHypothesesTest.partialUse

end Pythia.MinimizeHypothesesTest
