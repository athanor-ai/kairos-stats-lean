/-
Copyright (c) 2026 Pythia Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia

Pythia.Distributed.ByzantineQuorum — Byzantine quorum intersection theorem.

# Theorem

* `byzantine_quorum_intersection` — Under `n > 3f`, any two Byzantine
  quorums (sets with more than `(n + f) / 2` members) share at least one
  *correct* (non-faulty) member.

# Proof sketch

  |Q1 ∩ Q2| ≥ |Q1| + |Q2| - |nodes|   (inclusion-exclusion lower bound)
             > faulty.card              (from the two quorum-size hypotheses)

  Hence |(Q1 ∩ Q2) \ faulty| = |Q1 ∩ Q2| - |Q1 ∩ Q2 ∩ faulty|
                              ≥ |Q1 ∩ Q2| - |faulty|
                              > 0.

# References

Castro & Liskov, "Practical Byzantine Fault Tolerance", OSDI 1999, §4.
Bracha & Toueg, "Asynchronous Consensus and Broadcast Protocols",
  JACM 32(4), 1985.
-/
import Mathlib

namespace Pythia.Distributed

/-!
### byzantine_quorum_intersection

Under `n > 3f`, any two Byzantine quorums share a correct member.
-/

/-- **Byzantine quorum intersection** (ATH-940 §2, Castro-Liskov 1999 §4):
under `n > 3f`, any two Byzantine quorums share a correct (non-faulty) node. -/
theorem byzantine_quorum_intersection
    {α : Type*} [DecidableEq α] {nodes : Finset α}
    (faulty : Finset α) (hFaulty : faulty ⊆ nodes)
    (Q1 Q2 : Finset α) (hQ1 : Q1 ⊆ nodes) (hQ2 : Q2 ⊆ nodes)
    (hf : faulty.card * 3 < nodes.card)
    (hQ1_size : 2 * Q1.card > nodes.card + faulty.card)
    (hQ2_size : 2 * Q2.card > nodes.card + faulty.card) :
    ((Q1 ∩ Q2) \ faulty).Nonempty := by
  -- Step 1: establish |Q1 ∩ Q2| > faulty.card via inclusion-exclusion.
  have hInter_card : Q1.card + Q2.card - nodes.card ≤ (Q1 ∩ Q2).card := by
    have hle : (Q1 ∪ Q2).card ≤ nodes.card :=
      Finset.card_le_card (Finset.union_subset hQ1 hQ2)
    have heq := Finset.card_union_add_card_inter Q1 Q2
    omega
  have hInter_gt : (Q1 ∩ Q2).card > faulty.card := by
    omega
  -- Step 2: |(Q1 ∩ Q2) \ faulty| > 0 via card_sdiff bound.
  have hFaulty_inter : (faulty ∩ (Q1 ∩ Q2)).card ≤ faulty.card :=
    Finset.card_le_card (Finset.inter_subset_left)
  have hSdiff_pos : 0 < ((Q1 ∩ Q2) \ faulty).card := by
    have := Finset.card_sdiff_add_card_inter (Q1 ∩ Q2) faulty
    -- card_sdiff_add_card_inter : (s \ t).card + (s ∩ t).card = s.card
    -- so (Q1 ∩ Q2 \ faulty).card = (Q1 ∩ Q2).card - (Q1 ∩ Q2 ∩ faulty).card
    have hle2 : ((Q1 ∩ Q2) ∩ faulty).card ≤ faulty.card :=
      Finset.card_le_card (Finset.inter_subset_right)
    omega
  exact Finset.card_pos.mp hSdiff_pos

end Pythia.Distributed
