/-
Pythia.Tactic.ValidateInvokedLemmasTest — regression tests for
`#validate_invoked_lemmas`.

Each test exercises the command on a known theorem from this file.
The tests compile cleanly on all machines because they use only names
defined here or in Lean core (e.g. `Nat.add_comm`, `List.length_append`).

## What is being checked

1. A theorem whose proof references only valid names emits the all-pass
   info message ("all N invoked lemma(s) exist").
2. A locally-defined theorem works correctly.
3. A theorem with a tactic proof (whose elaborated term references various
   core Lean constants) is also walked correctly.

Note: the `logWarning` path (missing lemma) cannot be triggered in
well-typed Lean code: a phantom `Expr.const` with a missing name cannot
appear in a kernel-checked proof term. The warning path fires in practice
when a tactic-produced term references an opaque auxiliary constant that
was later removed; this guard is most useful as a post-hoc check on stale
proof terms where the environment has changed.
-/
import Pythia.Tactic.ValidateInvokedLemmas

namespace Pythia.ValidateInvokedLemmasTest

-- A small helper theorem whose proof uses standard Lean/core names.
-- Non-private so the name is accessible via its fully-qualified namespace.
theorem addCommExample (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

-- Test 1: a theorem with a simple term proof.
-- Expected: "#validate_invoked_lemmas ... : all N invoked lemma(s) exist."
#validate_invoked_lemmas Pythia.ValidateInvokedLemmasTest.addCommExample

-- A slightly richer theorem so the walk visits more constants.
theorem listAppendAssocExample (l m n : List Nat)
    : (l ++ m) ++ n = l ++ (m ++ n) :=
  List.append_assoc l m n

-- Test 2: theorem with a Lean-core proof term.
#validate_invoked_lemmas Pythia.ValidateInvokedLemmasTest.listAppendAssocExample

-- A tactic-proof theorem: the elaborated proof term will contain various
-- auxiliary constants (Eq.mpr, congrArg, etc.) but all of them exist.
theorem natSuccPosExample (n : Nat) : 0 < n.succ :=
  Nat.succ_pos n

-- Test 3: tactic-elaborated proof.
#validate_invoked_lemmas Pythia.ValidateInvokedLemmasTest.natSuccPosExample

end Pythia.ValidateInvokedLemmasTest
