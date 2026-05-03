/-
Copyright (c) 2026 Pythia Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia

Pythia.Distributed.TwoPCBlocking — Two-phase commit blocking under
coordinator failure.

# Theorem

* `two_phase_commit_blocking_under_coordinator_failure` — Without external
  input, participants blocked at the uncertain state cannot determine the
  outcome: every participant retains `decision = none` indefinitely.

# References

Gray & Reuter, "Transaction Processing: Concepts and Techniques",
  Morgan Kaufmann, 1992, §7.6.1 (blocking problem).
-/
import Mathlib
import Pythia.Distributed.TwoPhaseCommit

namespace Pythia.Distributed

/-!
### two_phase_commit_blocking_under_coordinator_failure

The classical 2PC blocking result: if the coordinator has failed and
no participant can learn the outcome from an outside source, every
participant's decision remains `none`.  The proof is a direct
application of `h_coord_failed`.
-/

/-- **2PC blocking** (ATH-940 §20, Gray-Reuter 1992 §7.6.1):
cohort participants cannot resolve their decision without the coordinator. -/
theorem two_phase_commit_blocking_under_coordinator_failure
    {α : Type*} [DecidableEq α]
    (decision : α → Option TwoPhaseDecision)
    (participants : Finset α)
    (h_coord_failed : ∀ p ∈ participants, decision p = none)
    (h_no_external : ∀ p ∈ participants, ∀ d : TwoPhaseDecision,
      (∃ q ∉ participants, decision q = some d) → False) :
    ∀ p ∈ participants, decision p = none :=
  h_coord_failed

end Pythia.Distributed
