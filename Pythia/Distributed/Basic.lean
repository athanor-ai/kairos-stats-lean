/-
Copyright (c) 2026 Pythia Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia
-/
import Mathlib

/-!
# Pythia.Distributed — Distributed-Systems Verification

This module formalizes core theorems from distributed-systems theory,
starting with the **Paxos quorum intersection** lemma and building toward
Paxos safety, FLP impossibility, CAP, Byzantine quorum intersection,
Lamport timestamps, two-phase commit, Raft safety, and PBFT.

## Main results

* `paxos_quorum_intersection`: any two strict-majority quorums of a finite
  node set share at least one common member.  This is the foundational
  property on which single-decree Paxos safety rests.
-/

namespace Pythia.Distributed

/-- **Paxos quorum intersection.** Any two majorities of a finite node set
share at least one common member. This is the foundational lemma underlying
single-decree Paxos safety: if two distinct ballots each gather a majority
quorum, the quorums must share a node, and the cross-ballot invariant on
that shared node forces agreement on the chosen value. -/
theorem paxos_quorum_intersection
    {α : Type*} [DecidableEq α] {nodes : Finset α}
    (Q1 Q2 : Finset α)
    (hQ1 : Q1 ⊆ nodes) (hQ2 : Q2 ⊆ nodes)
    (hQ1_maj : 2 * Q1.card > nodes.card)
    (hQ2_maj : 2 * Q2.card > nodes.card) :
    (Q1 ∩ Q2).Nonempty := by
  contrapose! hQ1_maj;
  -- Since $Q1$ and $Q2$ are disjoint and both are subsets of $nodes$, we have $|Q1 \cup Q2| = |Q1| + |Q2|$.
  have h_union : (Q1 ∪ Q2).card = Q1.card + Q2.card := by
    exact Finset.card_union_of_disjoint ( Finset.disjoint_iff_inter_eq_empty.mpr hQ1_maj );
  linarith [ Finset.card_le_card ( Finset.union_subset hQ1 hQ2 ) ]

end Pythia.Distributed