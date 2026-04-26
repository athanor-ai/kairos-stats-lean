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

/-- `#disprove_must_say_valid`: like `#disprove_must_fail`, but
additionally asserts the error message contains `VALID` or `no
counterexample`, the markers for the unsat-verdict path. We tolerate
the `notInstalled` fallback (`z3 binary not found on PATH`) so the
test still passes on machines without z3, where the tactic raises
for a different reason but we still don't want a soundness regression
where disprove silently SUCCEEDS on a true goal. The point of this
command is to lock in the "true goals get reported as VALID" contract
when z3 IS available.

If neither marker appears AND the message also does not mention
`not found on PATH`, the test fails loudly: disprove either raised
the wrong error or (worse) closed a true goal. -/
syntax (name := disproveMustSayValid)
  "#disprove_must_say_valid" "(" term ")" : command

@[command_elab disproveMustSayValid] def elabDisproveMustSayValid :
    CommandElab := fun stx => match stx with
  | `(#disprove_must_say_valid ($t)) => liftTermElabM do
      let goalType ← Term.elabTerm t (some (.sort .zero))
      let goalType ← instantiateMVars goalType
      let mvar ← Meta.mkFreshExprMVar (some goalType) MetavarKind.syntheticOpaque
      try
        let _ ← Tactic.run mvar.mvarId! do
          evalTactic (← `(tactic| intros))
          evalTactic (← `(tactic| disprove))
        -- This is the soundness regression: disprove RETURNED on a
        -- TRUE goal. It must always fail.
        logError m!"disprove unexpectedly closed a TRUE goal: {goalType}"
      catch e =>
        let msg ← e.toMessageData.toString
        let hasValid : Bool := (msg.splitOn "VALID").length > 1
        let hasNoCex : Bool := (msg.splitOn "no counterexample").length > 1
        let hasNotInstalled : Bool :=
          (msg.splitOn "not found on PATH").length > 1
        if hasValid || hasNoCex then
          logInfo m!"disprove (as expected) reported VALID on TRUE goal {goalType}:\n{msg}"
        else if hasNotInstalled then
          -- Acceptable on machines without z3; the soundness contract
          -- (no kernel close) is still honoured.
          logInfo m!"disprove fell through to notInstalled on {goalType}:\n{msg}"
        else
          logError m!"disprove raised an unexpected error on TRUE goal {goalType}: message contains neither `VALID`, `no counterexample`, nor `not found on PATH`. Got:\n{msg}"
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

-- Test 5 (`disprove_test_pseudo_squared_lower_bound`): the
-- statement `∀ x y, x * x ≥ y` looks tautological at first
-- glance (squares are nonneg) but is FALSE: pick `x = 0, y = 1`.
-- This is the classic "tautological-looking-but-false" trap.
-- The encoder linearises `x * x` with a fresh placeholder; the
-- LRA assignment finds a witness against the bare `x_sq ≥ y`
-- inequality even though the algebraic relation is dropped.
#disprove_must_fail (∀ (x y : ℝ), x * x ≥ y)

-- Test 6 (`disprove_test_boolean_predicate_over_reals`):
-- a Boolean predicate that LOOKS true but isn't. The claim "any
-- two reals satisfying `x < y` also satisfy `2 * x < y`" is a
-- false strengthening: counterexample `x = 0.1, y = 0.2`.
#disprove_must_fail (∀ (x y : ℝ), x < y → 2 * x < y)

-- Test 7 (`disprove_test_universally_quantified_falsehood`):
-- a flatly false universally-quantified arithmetic claim. There
-- are no hypotheses to relax: `∀ x, x ≥ 1` is false at any
-- `x < 1`.
#disprove_must_fail (∀ (x : ℝ), x ≥ 1)

/-! ### TRUE-statement regression tests

These cases assert that `disprove` on a TRUE goal reports the
goal-appears-VALID message instead of producing a witness. The
companion `#disprove_must_say_valid` command checks the error
message contents to detect a soundness regression where disprove
silently closes a true goal. Tolerant of the no-z3 fallback. -/

-- Test 8 (`disprove_test_true_reflexivity`): `∀ x, x ≤ x` is the
-- canonical TRUE statement under QF_LRA. z3 returns unsat;
-- disprove must raise with VALID / no-counterexample wording.
#disprove_must_say_valid (∀ (x : ℝ), x ≤ x)

-- Test 9 (`disprove_test_true_transitivity`): a textbook TRUE
-- statement: ≤-transitivity. z3 returns unsat under disprove; the
-- VALID branch must fire.
#disprove_must_say_valid (∀ (a b c : ℝ), a ≤ b → b ≤ c → a ≤ c)

end Pythia.DisproveTest
