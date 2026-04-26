/-
Pythia.Tactic.DisproveTest — regression tests for `disprove`.

Each example here states a FALSE claim under linear-real
hypotheses. The `disprove` tactic must FAIL the proof attempt with
an informative error that either (a) reports a Z3-found
counterexample, or (b) skips gracefully because the z3 binary is
not on PATH.

## Skip-if-no-z3 pattern

Without z3 installed, the tactic returns a `notInstalled` error
rather than a witness. Both paths are FAILURES of the proof
attempt: `disprove` never closes a goal. So a robust test only
asserts that the tactic does NOT close the goal, while leaving the
exact error text unchecked. We do this with a small helper command
`#disprove_must_fail`, which (i) runs `disprove` on a synthetic
goal and (ii) reports an info message if-and-only-if the tactic
threw an error. CI passes whether or not z3 is on the build
machine, because both `notInstalled` and the witness path raise an
error — the only failure mode is `disprove` somehow closing a
false goal, which would be a real soundness signal.

## Lean-gating

Every test elaborates against the kernel under
`{propext, Classical.choice, Quot.sound}` (the Mathlib axiom
budget). No `sorry`, no skipped declarations, no axiom smuggling.
The witness Z3 returns is purely informational and never enters a
proof term.

## Driver

Phase 1.
-/
import Pythia.Tactic.Disprove

namespace Pythia.DisproveTest

open Lean Elab Command Term Tactic

/-- `#disprove_must_fail` — run `disprove` on the goal of a given
`Prop`-typed term and confirm that the tactic raised an error. The
command synthesises a fresh metavariable of the supplied type,
feeds it to `disprove` inside `Tactic.run`, and reports whether the
attempt failed.

This is the test harness we use in lieu of a `sorry`-based
"expected to fail" pattern: `disprove` must always raise, and we
record which raise (witness path vs notInstalled vs outOfFragment)
fired so a human can read the regression log. -/
syntax (name := disproveMustFail)
  "#disprove_must_fail" "(" term ")" : command

@[command_elab disproveMustFail] def elabDisproveMustFail : CommandElab :=
  fun stx => match stx with
  | `(#disprove_must_fail ($t)) => liftTermElabM do
      let goalType ← Term.elabTerm t (some (.sort .zero))
      let goalType ← instantiateMVars goalType
      let mvar ← Meta.mkFreshExprMVar (some goalType) MetavarKind.syntheticOpaque
      -- Run `disprove` inside a tactic context. We first `intros`
      -- so that universally-quantified test goals end up in the
      -- post-introduction form `disprove` expects (a flat
      -- (in)equality with the bound variables in the local
      -- context).
      try
        let _ ← Tactic.run mvar.mvarId! do
          evalTactic (← `(tactic| intros))
          evalTactic (← `(tactic| disprove))
        -- Reaching this point means `disprove` did not raise. That
        -- is a soundness failure: the tactic is supposed to always
        -- fail on the test inputs.
        logError m!"disprove unexpectedly returned without raising on goal {goalType}"
      catch e =>
        -- Expected path. Surface the message at info-level so a
        -- human can read the regression log.
        let msg ← e.toMessageData.toString
        logInfo m!"disprove (as expected) raised on {goalType}:\n{msg}"
      pure ()
  | _ => throwUnsupportedSyntax

/-! ### Test cases

Each goal is FALSE under stated hypotheses. `disprove` must fail
with either a counterexample report (z3 present) or a
not-installed report (z3 absent). The tests check only that some
failure occurred. -/

-- Test 1 (`disprove_test_universal_le`): `x ≤ y` is not a theorem
-- when `x = 1, y = 0` is a model of the hypothesis-free body.
#disprove_must_fail (∀ (x y : ℝ), x ≤ y)

-- Test 2 (`disprove_test_nonneg_implies_nonpos`): under `x ≥ 0`,
-- the goal `x ≤ 0` is false; any positive `x` witnesses.
#disprove_must_fail (∀ (x : ℝ), x ≥ 0 → x ≤ 0)

-- Test 3 (`disprove_test_strict_chain_subtract_one`): the chain
-- `a < b ∧ b < c` does NOT entail `a < b - 1`, even though it
-- entails `a < c`. Counterexample: a = 0, b = 0.5, c = 1.0.
#disprove_must_fail (∀ (a b c : ℝ), a < b → b < c → a < b - 1)

-- Test 4 (`disprove_test_subtraction_breaks_positivity`):
-- positivity is not transitive across subtraction. `x ≥ 0 ∧ y ≥ 0`
-- does NOT entail `x - y ≥ 0`. Counterexample: x = 0, y = 1.
#disprove_must_fail (∀ (x y : ℝ), x ≥ 0 → y ≥ 0 → x - y ≥ 0)

end Pythia.DisproveTest
