/-
Pythia.Distributed.PaxosCorollaries — Paxos single-decree consensus corollaries.

# Theorems

* `paxos_no_two_leaders` — At most one leader per ballot: any two majorities
  of a finite node set share a member (quorum-intersection corollary).
  Corollary of `paxos_quorum_intersection` (in Pythia.Distributed.Basic via
  Aristotle starter a3968b8b). Proved standalone here by the same arithmetic.

* `paxos_prepare_response_uniqueness` — Phase-1b response function is
  well-defined: a node returns at most one (ballot, value) pair per
  prepare-ballot. Proof: `Option.some` injectivity.

# References

Lamport, "Paxos Made Simple", ACM SIGACT News 32(4), 2001.
Lamport, "The Part-Time Parliament", ACM TOCS 16(2), 1998.
-/
import Mathlib

namespace Pythia.Distributed

/-!
### Local quorum-intersection helper

This is a private copy of the quorum-intersection arithmetic so that
`PaxosCorollaries.lean` builds standalone.  The canonical public theorem
`paxos_quorum_intersection` lives in `Pythia.Distributed.Basic` (created by
the Aristotle starter a3968b8b-2cea-4dc8-b9a4-6185f8ec3537).  The private
name avoids a clash when both files are imported.
-/

private lemma _quorum_intersection_helper {α : Type*} [DecidableEq α] {nodes : Finset α}
    (Q1 Q2 : Finset α) (hQ1 : Q1 ⊆ nodes) (hQ2 : Q2 ⊆ nodes)
    (h_card1 : 2 * Q1.card > nodes.card) (h_card2 : 2 * Q2.card > nodes.card) :
    (Q1 ∩ Q2).Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  have hd : Q1.card + Q2.card ≤ nodes.card := by
    have := Finset.card_union_add_card_inter Q1 Q2
    rw [h_empty, Finset.card_empty] at this
    have hle : (Q1 ∪ Q2).card ≤ nodes.card :=
      Finset.card_le_card (Finset.union_subset hQ1 hQ2)
    omega
  omega

/-!
### paxos_no_two_leaders

In any ballot, two quorums (sets of nodes that form a voting majority)
must intersect.  Consequently, no two distinct leaders can both hold
majorities simultaneously — they must share at least one witness node.

The statement is exactly the quorum-intersection property recast as the
"no two leaders" safety condition.  Proof: `Finset.card_union_add_card_inter`
plus `omega` arithmetic.
-/

/-- **Paxos no-two-leaders** (ATH-940 §3): any two majority quorums of a
finite node set share a member. -/
theorem paxos_no_two_leaders {α : Type*} [DecidableEq α] {nodes : Finset α}
    (Q1 Q2 : Finset α) (hQ1 : Q1 ⊆ nodes) (hQ2 : Q2 ⊆ nodes)
    (h_card1 : 2 * Q1.card > nodes.card) (h_card2 : 2 * Q2.card > nodes.card) :
    (Q1 ∩ Q2).Nonempty :=
  _quorum_intersection_helper Q1 Q2 hQ1 hQ2 h_card1 h_card2

/-!
### paxos_prepare_response_uniqueness

In Phase 1b of Paxos, each acceptor replies to a Prepare(b) message with
at most one (highest-accepted-ballot, value) pair.  This is a direct
consequence of function determinism: if `highestAccepted n b = some r1`
and `highestAccepted n b = some r2` then `r1 = r2` by `Option.some`
injectivity.
-/

/-- **Paxos Phase-1b uniqueness** (ATH-940 §5): the prepare-response
function is well-defined — a node returns a unique (ballot, value) pair. -/
theorem paxos_prepare_response_uniqueness
    {α : Type*} {ballot : Type*} [LinearOrder ballot] {V : Type*} [DecidableEq V]
    (highestAccepted : α → ballot → Option (ballot × V))
    (n : α) (b : ballot) (r1 r2 : ballot × V)
    (h1 : highestAccepted n b = some r1) (h2 : highestAccepted n b = some r2) :
    r1 = r2 := by
  have : some r1 = some r2 := h1 ▸ h2
  exact Option.some.inj this

end Pythia.Distributed
