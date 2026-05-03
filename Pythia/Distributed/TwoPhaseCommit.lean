/-
Pythia.Distributed.TwoPhaseCommit — Two-Phase Commit (2PC) protocol theorems.

# Inductive types

* `TwoPhaseDecision` — coordinator / cohort decision: `Commit` or `Abort`.
* `TwoPhaseVote`     — cohort vote: `Yes` or `No`.

# Theorems

* `two_phase_commit_agreement` — If any participant commits, no participant
  aborts.  Proof: if some p2 aborted then `hAbortIfAnyNo` gives a No-voter,
  but `hCommitRequiresAllYes` (from the committing p1) says all voters said
  Yes — contradiction.

* `two_phase_commit_validity` — All-yes implies existence of a commit.
  The hypothesis is exactly this implication; proof is `exact hAllYesCommit`.

# References

Gray & Reuter, "Transaction Processing: Concepts and Techniques",
  Morgan Kaufmann, 1992, §7.4.2.
-/
import Mathlib

namespace Pythia.Distributed

/-- Coordinator or cohort decision in 2PC. -/
inductive TwoPhaseDecision | Commit | Abort
  deriving DecidableEq

/-- Cohort vote in Phase 1 of 2PC. -/
inductive TwoPhaseVote | Yes | No
  deriving DecidableEq

/-!
### two_phase_commit_agreement

Safety: it is impossible for one participant to commit while another aborts.
The proof derives a contradiction: a commit at p1 forces every voter to Yes
(via `hCommitRequiresAllYes`), but an abort at p2 requires some No-voter
(via `hAbortIfAnyNo`).
-/

/-- **2PC agreement** (ATH-940 §18, Gray-Reuter 1992 §7.4.2):
no participant commits while another aborts. -/
theorem two_phase_commit_agreement
    {α : Type*} [DecidableEq α]
    (decision : α → TwoPhaseDecision) (vote : α → TwoPhaseVote)
    (hCommitRequiresAllYes : ∀ p : α, decision p = TwoPhaseDecision.Commit →
      ∀ q : α, vote q = TwoPhaseVote.Yes)
    (hAbortIfAnyNo : ∀ p : α, decision p = TwoPhaseDecision.Abort →
      ∃ q : α, vote q = TwoPhaseVote.No)
    (p1 p2 : α) :
    decision p1 = TwoPhaseDecision.Commit →
    decision p2 ≠ TwoPhaseDecision.Abort := by
  intro hCommit hAbort
  obtain ⟨q, hNo⟩ := hAbortIfAnyNo p2 hAbort
  have hYes : vote q = TwoPhaseVote.Yes := hCommitRequiresAllYes p1 hCommit q
  rw [hYes] at hNo
  exact TwoPhaseVote.noConfusion hNo

/-!
### two_phase_commit_validity

Liveness (conditional): if the protocol guarantees a commit whenever all
votes are Yes, then the all-yes condition implies the existence of a commit.
The proof names the hypothesis.
-/

/-- **2PC validity** (ATH-940 §19, Gray-Reuter 1992 §7.4.2):
all-yes implies some participant commits. -/
theorem two_phase_commit_validity
    {α : Type*} [DecidableEq α] [Fintype α] [Nonempty α]
    (decision : α → TwoPhaseDecision) (vote : α → TwoPhaseVote)
    (hAllYesCommit : (∀ q : α, vote q = TwoPhaseVote.Yes) →
      ∃ p : α, decision p = TwoPhaseDecision.Commit) :
    (∀ q : α, vote q = TwoPhaseVote.Yes) →
    ∃ p : α, decision p = TwoPhaseDecision.Commit :=
  hAllYesCommit

end Pythia.Distributed
